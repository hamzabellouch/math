import OAI.NumberTheory.DukePrimeDegree.Geometry.EliminationMatrixCoordinates
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingRootCoordinates

namespace OAI

/-! # Conjugation acts by elementary row shears on the remaining root group -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma conjugation_entry_of_standard_column {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (g : G n) (hcol : ∀ i, g.val i a = if i = a then 1 else 0)
    (hbb : g.val b b = 1) (r : ℝ) (i j : Fin n) :
    ((Matrix.SpecialLinearGroup.transvection hab (-r)) * g *
      Matrix.SpecialLinearGroup.transvection hab r).val i j =
      if i = a then if j = b then g.val a b else g.val a j - r * g.val b j
      else g.val i j := by
  change ((Matrix.transvection a b (-r) * g.val) * Matrix.transvection a b r) i j = _
  by_cases hi : i = a
  · subst i
    by_cases hj : j = b
    · subst j
      rw [Matrix.mul_transvection_apply_same,Matrix.transvection_mul_apply_same,
        Matrix.transvection_mul_apply_same,hbb,hcol a,hcol b]
      simp [Ne.symm hab]
    · rw [Matrix.mul_transvection_apply_of_ne (i := a) (j := b) a j hj,
        Matrix.transvection_mul_apply_same]
      simp [hj,sub_eq_add_neg]
  · by_cases hj : j = b
    · subst j
      rw [Matrix.mul_transvection_apply_same,
        Matrix.transvection_mul_apply_of_ne (i := a) (j := b) i b hi,
        Matrix.transvection_mul_apply_of_ne (i := a) (j := b) i a hi,hcol i]
      simp [hi]
    · rw [Matrix.mul_transvection_apply_of_ne (i := a) (j := b) i j hj,
        Matrix.transvection_mul_apply_of_ne (i := a) (j := b) i j hi]
      simp [hi]

end DukePrimeDegree

end

end OAI
