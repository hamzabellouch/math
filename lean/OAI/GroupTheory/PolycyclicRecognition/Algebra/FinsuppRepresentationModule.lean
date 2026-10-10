import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteIntegralRepresentations
import Mathlib.RingTheory.Finiteness.Finsupp

namespace OAI

/-! # The group-ring module of a direct sum of representations -/

noncomputable section
namespace PolycyclicRecognition

open Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] (G : Type) [Group G] (α : Type) (A : Rep k G)

def finsuppRepresentationModuleEquiv :
    (α →₀ A.ρ.asModule) ≃ₗ[k[G]] (Rep.finsupp α A).ρ.asModule where
  toAddEquiv := (Finsupp.mapRange.addEquiv A.ρ.asModuleEquiv.toAddEquiv).trans
    (Rep.finsupp α A).ρ.asModuleEquiv.symm.toAddEquiv
  map_smul' r v := by
    apply (Rep.finsupp α A).ρ.asModuleEquiv.injective
    let e := Finsupp.mapRange.linearEquiv (α := α) A.ρ.asModuleEquiv
    change e (r • v) = (A.ρ.finsupp α).asAlgebraHom r (e v)
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r s hr hs => simp only [add_smul, map_add, hr, hs, LinearMap.add_apply]
    | single g c =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v w hv hw => simp only [smul_add, map_add, hv, hw]
      | single i a =>
        simp [e, Representation.asAlgebraHom_single, Representation.finsupp_single]
        ext j
        rfl


end PolycyclicRecognition

end

end OAI
