import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.ReindexHomology
import OAI.GroupTheory.SimpleAmenable.Configurations.TrajectoryFaces
import OAI.GroupTheory.SimpleAmenable.Homology.TrajectoryTensor

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
open scoped TensorProduct
namespace SimpleAmenable.PolygonObject.LabelledStage
open Labelled

variable {a n : ℕ} {K : Type} [AddCommGroup K]
abbrev RankTwo := Multiplicative (ℤ×ℤ)
noncomputable def negativeProjection (u : CutRing × CutRing) : RankTwo :=
  (SquareStep.orbitProjection (Multiplicative.ofAdd u))⁻¹
lemma negativeProjection_add (u v : CutRing × CutRing) :
    negativeProjection (u+v)=negativeProjection u*negativeProjection v := by
  change (SquareStep.orbitProjection (Multiplicative.ofAdd u*Multiplicative.ofAdd v))⁻¹ = _
  rw [map_mul,mul_inv_rev,mul_comm]
  rfl

noncomputable def signedLabelEquiv (n : ℕ) : ReducedLabel n ≃ (Fin n → RankTwo) :=
  (reducedLabelEquiv n).trans (Equiv.piCongrRight (fun _ => Equiv.inv RankTwo))
lemma signedLabelEquiv_apply (l : ReducedLabel n) (i : Fin n) :
    signedLabelEquiv n l i=negativeProjection (l.val i) := rfl
lemma signedLabel_zero_face (l : ReducedLabel (n+1)) :
    signedLabelEquiv n (labelMap (reindexLabel (faceFunctor 0))
      (reindexLabel_reduced (faceFunctor 0)) l)=Fin.tail (signedLabelEquiv (n+1) l) := by
  change (fun i => negativeProjection (reindexLabel (faceFunctor 0) l.val i)) = _
  rw [reindexLabel_zero_face]
  rfl
lemma signedLabel_succ_face (l : ReducedLabel (n+1)) (i : Fin (n+1)) :
    signedLabelEquiv n (labelMap (reindexLabel (faceFunctor i.succ))
      (reindexLabel_reduced (faceFunctor i.succ)) l)=i.contractNth (·*·) (signedLabelEquiv (n+1) l) := by
  change (fun k => negativeProjection (reindexLabel (faceFunctor i.succ) l.val k)) = _
  rw [reindexLabel_succ_face]
  exact Fin.comp_contractNth (·+·) (·*·) negativeProjection_add i l.val
noncomputable def chainCoordinates (a n : ℕ) (K : Type) [AddCommGroup K] :
    Coefficients a n K ≃ₗ[ℤ] ((Fin n → RankTwo) →₀ (SquareStep a ⊗[ℤ] K)) :=
  (Finsupp.mapRange.linearEquiv (BooleanStep.tensorEquiv (a:=a) (K:=K)).symm).trans
    (Finsupp.domLCongr (signedLabelEquiv n))
lemma chainCoordinates_single (l : ReducedLabel n) (v : BooleanStep a K) :
    chainCoordinates a n K (Finsupp.single l v)=
      Finsupp.single (signedLabelEquiv n l) ((BooleanStep.tensorEquiv (a:=a) (K:=K)).symm v) := by
  simp [chainCoordinates]
lemma chainCoordinates_zero_face (l : ReducedLabel (n+1)) (v : BooleanStep a K) :
    chainCoordinates a n K (reindexCoefficients (K:=K) (faceFunctor 0) (Finsupp.single l v)) =
      Finsupp.single (Fin.tail (signedLabelEquiv (n+1) l))
        ((SquareStep.coefficientRep a K).ρ ((signedLabelEquiv (n+1) l 0)⁻¹)
          ((BooleanStep.tensorEquiv (a:=a) (K:=K)).symm v)) := by
  rw [reindexCoefficients_single,chainCoordinates_single,signedLabel_zero_face,
    initialDisplacement_zero_face,tensorEquiv_symm_translation]
  simp only [signedLabelEquiv_apply,negativeProjection,inv_inv]
  rfl
lemma chainCoordinates_succ_face (l : ReducedLabel (n+1)) (v : BooleanStep a K) (i : Fin (n+1)) :
    chainCoordinates a n K (reindexCoefficients (K:=K) (faceFunctor i.succ) (Finsupp.single l v)) =
      Finsupp.single (i.contractNth (·*·) (signedLabelEquiv (n+1) l))
        ((BooleanStep.tensorEquiv (a:=a) (K:=K)).symm v) := by
  rw [reindexCoefficients_single,chainCoordinates_single,signedLabel_succ_face,
    initialDisplacement_succ_face,stepTranslate_zero]
end SimpleAmenable.PolygonObject.LabelledStage

end

end OAI
