// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Error Reporting for Anonymous Region Lifetime Errors
//! where both the regions are anonymous.
use hir;
use infer::InferCtxt;
use ty::{self, Region};
use infer::region_inference::RegionResolutionError::*;
use infer::region_inference::RegionResolutionError;
use hir::map as hir_map;
use middle::resolve_lifetime as rl;
use hir::intravisit::{self, Visitor, NestedVisitorMap};
use syntax_pos::Span;

// The visitor captures the corresponding `hir::Ty` of the
// anonymous region.
struct FindNestedTypeVisitor<'a, 'gcx: 'a + 'tcx, 'tcx: 'a> {
    infcx: &'a InferCtxt<'a, 'gcx, 'tcx>,
    hir_map: &'a hir::map::Map<'gcx>,
    bound_region: ty::BoundRegion,
    found_type: Option<&'gcx hir::Ty>,
    is_struct: bool,
}

struct TyPathVisitor<'a, 'gcx: 'a + 'tcx, 'tcx: 'a> {
    infcx: &'a InferCtxt<'a, 'gcx, 'tcx>,
    hir_map: &'a hir::map::Map<'gcx>,
    found_it: bool,
    bound_region: ty::BoundRegion,
}

impl<'a, 'gcx, 'tcx> Visitor<'gcx> for TyPathVisitor<'a, 'gcx, 'tcx> {
    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'gcx> {
        NestedVisitorMap::OnlyBodies(&self.hir_map)
    }

    fn visit_lifetime(&mut self, lifetime: &hir::Lifetime) {
        let br_index = match self.bound_region {
            ty::BrAnon(index) => index,
            _ => return,
        };


        match self.infcx.tcx.named_region_map.defs.get(&lifetime.id) {
            // the lifetime of the TyPath!
            Some(&rl::Region::LateBoundAnon(debuijn_index, anon_index)) => {
                if debuijn_index.depth == 1 && anon_index == br_index {
                    self.found_it = true;

                    debug!("executing loop debuijn_index.depth={:?}
 anon_index= {:},branon_index={:?} ",
                           debuijn_index.depth,
                           anon_index,
                           br_index);
                }
            }
            Some(&rl::Region::Static) |
            Some(&rl::Region::EarlyBound(_, _)) |
            Some(&rl::Region::LateBound(_, _)) |
            Some(&rl::Region::Free(_, _)) |
            None => {
                debug!("no arg found");
            }
        }
    }

    fn visit_ty(&mut self, arg: &'gcx hir::Ty) {
        // ignore nested types
        //
        // If you have a type like `Foo<'a, &Ty>` we
        // are only interested in the immediate lifetimes ('a).
        //
        // Making `visit_ty` empty will ignore the `&Ty` embedded
        // inside, it will get reached by the outer visitor.
        debug!("arg is {:?}", arg);
    }
}

impl<'a, 'gcx, 'tcx> Visitor<'gcx> for FindNestedTypeVisitor<'a, 'gcx, 'tcx> {
    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'gcx> {
        NestedVisitorMap::OnlyBodies(&self.hir_map)
    }

    fn visit_ty(&mut self, arg: &'gcx hir::Ty) {
        // Find the index of the anonymous region that was part of the
        // error. We will then search the function parameters for a bound
        // region at the right depth with the same index.
        let br_index = match self.bound_region {
            ty::BrAnon(index) => index,
            _ => return,
        };

        match arg.node {
            hir::TyRptr(ref lifetime, _) => {
                match self.infcx.tcx.named_region_map.defs.get(&lifetime.id) {
                    // the lifetime of the TyRptr!
                    Some(&rl::Region::LateBoundAnon(debuijn_index, anon_index)) => {
                        if debuijn_index.depth == 1 && anon_index == br_index {
                            self.found_type = Some(arg);
                            return; // we can stop visiting now
                        }
                    }
                    Some(&rl::Region::Static) |
                    Some(&rl::Region::EarlyBound(_, _)) |
                    Some(&rl::Region::LateBound(_, _)) |
                    Some(&rl::Region::Free(_, _)) |
                    None => {
                        debug!("no arg found");
                    }
                }
            }
            hir::TyPath(_) => {
                debug!("Typath node 2 {:?}", arg);
                let mut subvisitor = &mut TyPathVisitor {
                                              infcx: self.infcx,
                                              found_it: false,
                                              bound_region: self.bound_region,
                                              hir_map: self.hir_map,
                                          };
                intravisit::walk_ty(subvisitor, arg); //  call walk_ty; as visit_ty is empty,
                // this will visit only outermost type
                if subvisitor.found_it {
                    self.is_struct = true;
                    self.found_type = Some(arg);
                    debug!("so struct detected, index = {:?}", subvisitor.found_it);
                } else {
                    debug!("visit.found_it == None");
                }

            }

            _ => {}
        }
        intravisit::walk_ty(self, arg);
    }
}

impl<'a, 'gcx, 'tcx> InferCtxt<'a, 'gcx, 'tcx> {
    // This function calls the `visit_ty` method for the parameters
    // corresponding to the anonymous regions. The `nested_visitor.found_type`
    // contains the anonymous type.
    pub fn find_anon_type(&self,
                          region: Region<'tcx>,
                          br: &ty::BoundRegion)
                          -> Option<(&hir::Ty, bool)> {
        if let Some(anon_reg) = self.is_suitable_anonymous_region(region) {
            let (def_id, _) = anon_reg;
            if let Some(node_id) = self.tcx.hir.as_local_node_id(def_id) {
                let ret_ty = self.tcx.type_of(def_id);
                if let ty::TyFnDef(_, _) = ret_ty.sty {
                    if let hir_map::NodeItem(it) = self.tcx.hir.get(node_id) {
                        if let hir::ItemFn(ref fndecl, _, _, _, _, _) = it.node {
                            return fndecl
                                       .inputs
                                       .iter()
                                       .filter_map(|arg| {
                                let mut nested_visitor = FindNestedTypeVisitor {
                                    infcx: &self,
                                    hir_map: &self.tcx.hir,
                                    bound_region: *br,
                                    found_type: None,
                                    is_struct: false,
                                };
                                nested_visitor.visit_ty(&**arg);
                                debug!("ft = {:?} bool={:?}",
                                       nested_visitor.found_type,
                                       nested_visitor.is_struct);
                                nested_visitor
                                    .found_type
                                    .map(|found_type| (found_type, nested_visitor.is_struct))
                            })
                                       .next();
                        }
                    }
                }
            }
        }
        None
    }

    pub fn try_report_anon_anon_conflict(&self, error: &RegionResolutionError<'tcx>) -> bool {

        let (span, sub, sup) = match *error {
            ConcreteFailure(ref origin, sub, sup) => (origin.span(), sub, sup),
            _ => return false, // inapplicable
        };

        let (ty1, ty2) = if self.is_suitable_anonymous_region(sup).is_some() &&
                            self.is_suitable_anonymous_region(sub).is_some() {
            if let (Some(anon_reg1), Some(anon_reg2)) =
                (self.is_suitable_anonymous_region(sup), self.is_suitable_anonymous_region(sub)) {
                let ((_, br1), (_, br2)) = (anon_reg1, anon_reg2);
                if self.find_anon_type(sup, &br1).is_some() &&
                   self.find_anon_type(sub, &br2).is_some() {
                    if let (Some(anon_type1), Some(anon_type2)) =
                        (self.find_anon_type(sup, &br1), self.find_anon_type(sub, &br2)) {
                        let ((anonarg_1, is_struct_1), (anonarg_2, is_struct_2)) = (anon_type1,
                                                                                    anon_type2);
                        if is_struct_1 || is_struct_2 {
                            return self.try_report_struct_anon_anon_conflict(anonarg_1,
                                                                             anonarg_2,
                                                                             is_struct_1,
                                                                             is_struct_2,
                                                                             span,
<<<<<<< HEAD
                                                                             sup,
                                                                             sub);
=======
sup,
sub);
>>>>>>> 122b4d2... non working changes

                        } else {
                            (anonarg_1, anonarg_2)
                        }
                    } else {
                        return false;
                    }
                } else {
                    return false;
                } // after this add
            } else {
                return false;
            }
        } else {
            return false; // inapplicable
        };
        debug!("{:?} and {:?}", ty1, ty2);
            if let Some(error_label) = self.process_anon_anon_error(sup,sub){
            let (span_label_var1, span_label_var2) = error_label;

            struct_span_err!(self.tcx.sess, span, E0623, "lifetime mismatch")
                .span_label(ty1.span,
                            format!("these references must have the same lifetime"))
                .span_label(ty2.span, format!(""))
                .span_label(span,
                            format!("data {} flows {} here", span_label_var1, span_label_var2))
                .emit();
            return true;
        } else {
            return false;
        }
 }

    fn try_report_struct_anon_anon_conflict(&self,
                                            ty1: &hir::Ty,
                                            ty2: &hir::Ty,
                                            is_arg1_struct: bool,
                                            is_arg2_struct: bool,
                                            span: Span,
                                            sup: Region<'tcx>,
                                            sub: Region<'tcx>)
                                            -> bool {
        let arg1_label = {
            if is_arg1_struct && is_arg2_struct {
                format!("these two structs are declared with different lifetimes...")
            } else if is_arg1_struct && !is_arg2_struct {
                format!("the struct and reference are declared with different lifetimes")
            } else {
                format!("the reference and struct are declared with different lifetimes")
            }
        };
        if let Some(label) = self.process_anon_anon_error(sup, sub) {
            let (label1, label2) = label;
            struct_span_err!(self.tcx.sess, span, E0624, "lifetime mismatch")
                .span_label(ty1.span, format!("{}", arg1_label))
                .span_label(ty2.span, format!(""))
                .span_label(span,format!("data {} flows {} here", label1, label2))
                .emit();
        } else {
            return false;
        }
        true

    }

  fn process_anon_anon_error(&self,sup: Region<'tcx>, sub: Region<'tcx> )->Option<(String,String)>{

  if let (Some(sup_arg), Some(sub_arg)) =
            (self.find_arg_with_anonymous_region(sup, sup),
             self.find_arg_with_anonymous_region(sub, sub)) {
            let ((anon_arg1, _, _, _), (anon_arg2, _, _, _)) = (sup_arg,
 sub_arg);
  let span_label_var1 = if let Some(simple_name) = anon_arg1.pat.simple_name() {
                format!("from `{}`", simple_name)
            } else {
                format!("")
            };

            let span_label_var2 = if let Some(simple_name) = anon_arg2.pat.simple_name() {
                format!("into `{}`", simple_name)
            } else {
                format!("")
            };

            Some((span_label_var1, span_label_var2))
        } else {
            None
        }
    }
}
