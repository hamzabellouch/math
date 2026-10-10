import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingDiagonal

namespace OAI

/-!
# Relative matrices after diagonal and root translation

These identities track the right-action convention in the return-pair
argument. After simultaneous root translation by `t`, the relative
matrix is conjugated by the root element at `-t`.
-/

noncomputable section
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootPairConjugate_rightAction {n : ℕ} (i j : Fin n)
    (x : X n) (g : G n) (τ : ℝ) :
    rightAction (rightAction x (rootPairFlow i j (-τ))) (rootPairConjugate i j τ g) =
      rightAction (rightAction x g) (rootPairFlow i j (-τ)) := by
  simp only [rootPairConjugate, rootPairFlow, diagonalOneParameter_neg,
    rightAction_mul, ← mul_assoc, inv_mul_cancel, one_mul]

lemma rootConjugate_rightAction {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (x : X n) (g : G n) (t : ℝ) :
    rightAction (rightAction x (Matrix.SpecialLinearGroup.transvection hij t))
      (Matrix.SpecialLinearGroup.transvection hij (-t) * g *
        Matrix.SpecialLinearGroup.transvection hij t) =
      rightAction (rightAction x g) (Matrix.SpecialLinearGroup.transvection hij t) := by
  have hcancel : Matrix.SpecialLinearGroup.transvection hij t *
      Matrix.SpecialLinearGroup.transvection hij (-t) = 1 := by
    rw [← Matrix.SpecialLinearGroup.transvection_add, add_neg_cancel]
    simp
  simp only [rightAction_mul, ← mul_assoc, hcancel, one_mul]

end DukePrimeDegree

end

end OAI
