import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.Definitions

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped InnerProductSpace ENNReal
open Kaplansky

abbrev ActualRepresentationHilbert := lp (fun z : ActualTestIndex => ActualHilbert z) 2

def actualFaithfulMap (a : ActualAlgebra) : ActualRepresentationHilbert →L[ℂ] ActualRepresentationHilbert :=
  lp.mapCLM 2 (fun z => actualRepresentation z a) (norm_nonneg a) (fun z => actualRepresentation_norm z a)

@[simp] lemma actualFaithfulMap_apply (a : ActualAlgebra) (x : ActualRepresentationHilbert) (z : ActualTestIndex) :
    actualFaithfulMap a x z = actualRepresentation z a (x z) := rfl

lemma actualFaithfulMap_star (a : ActualAlgebra) : actualFaithfulMap (star a) = star (actualFaithfulMap a) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr; intro z
  simp only [actualFaithfulMap_apply,map_star]
  exact (actualRepresentation z a).adjoint_inner_left _ _

def actualFaithfulRepresentation : ActualAlgebra →⋆ₐ[ℂ] (ActualRepresentationHilbert →L[ℂ] ActualRepresentationHilbert) where
  toFun := actualFaithfulMap
  map_zero' := by ext; rfl
  map_one' := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl
  commutes' _ := by ext; rfl
  map_star' := actualFaithfulMap_star

lemma actualFaithfulRepresentation_injective : Function.Injective actualFaithfulRepresentation := by
  classical
  intro a b hab
  apply Subtype.ext
  apply lp.ext
  apply funext
  intro z
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun T : ActualRepresentationHilbert →L[ℂ] ActualRepresentationHilbert =>
    T (lp.single (E:=fun z : ActualTestIndex => ActualHilbert z) 2 z v) z) hab
  change (a.val z) ((lp.single (E:=fun z : ActualTestIndex => ActualHilbert z) 2 z v) z) = (b.val z) ((lp.single (E:=fun z : ActualTestIndex => ActualHilbert z) 2 z v) z) at h
  simpa only [lp.single_apply_self] using h


end KaplanskyConsequences

end

end OAI
