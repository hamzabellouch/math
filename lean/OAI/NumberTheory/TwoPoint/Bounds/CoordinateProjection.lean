import OAI.NumberTheory.TwoPoint.Bounds.MatrixAction
import OAI.NumberTheory.TwoPoint.Bounds.SpectralTransfer

namespace OAI

/-! The orthogonal projection deleting the high-degree vertices. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def coordinateProjection (keep : V → Prop) :
    EuclideanSpace ℂ V →L[ℂ] EuclideanSpace ℂ V :=
  matrixOperator (Matrix.diagonal (fun i => if keep i then (1 : ℂ) else 0))

lemma coordinateProjection_apply (keep : V → Prop) (v : EuclideanSpace ℂ V) (i : V) :
    coordinateProjection keep v i = if keep i then v i else 0 := by
  change (∑ j, Matrix.diagonal (fun i => if keep i then (1 : ℂ) else 0) i j * v j) = _
  simp [Matrix.diagonal_apply]

lemma coordinateProjection_selfAdjoint (keep : V → Prop) :
    IsSelfAdjoint (coordinateProjection keep) := by
  apply matrixOperator_selfAdjoint
  intro i j
  by_cases hij : i = j
  · subst j
    by_cases hi : keep i <;> simp [hi]
  · simp [hij, Ne.symm hij]

lemma coordinateProjection_idempotent (keep : V → Prop) :
    coordinateProjection keep * coordinateProjection keep = coordinateProjection keep := by
  ext v i
  change coordinateProjection keep (coordinateProjection keep v) i = coordinateProjection keep v i
  simp only [coordinateProjection_apply]
  split_ifs <;> rfl

lemma coordinateProjection_support (keep : V → Prop) (v : EuclideanSpace ℂ V)
    (hv : coordinateProjection keep v = v) (i : V) (hi : v i ≠ 0) : keep i := by
  by_contra hkeep
  have he := congrArg (fun w : EuclideanSpace ℂ V => w i) hv
  rw [coordinateProjection_apply, ite_eq_right hkeep] at he
  exact hi he.symm

lemma coordinateProjection_norm_le (keep : V → Prop) (v : EuclideanSpace ℂ V) :
    ‖coordinateProjection keep v‖ ≤ ‖v‖ :=
  projection_norm_apply_le _ (coordinateProjection_selfAdjoint keep)
    (coordinateProjection_idempotent keep) v

end TwoPointCorrelations

end OAI
