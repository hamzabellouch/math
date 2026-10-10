import OAI.Analysis.Laughlin.Polynomial.AntisymmetricCoordinates
import OAI.Analysis.Laughlin.Spin.GenericOrthogonality

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairCoupledTensor_orthogonal (Q r s n m : ℕ) (hr : r ≤ Q) (hs : s ≤ Q)
    (hne : r ≠ s ∨ n ≠ m) :
    (∑ i, pairCoupledTensor Q r hr n i * pairCoupledTensor Q s hs m i) = 0 := by
  unfold pairCoupledTensor
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    _ = ((-1 : ℝ)^r * (-1 : ℝ)^s) *
      (∑ i, genericUnitDescendant Q Q r hr hr n i * genericUnitDescendant Q Q s hs hs m i) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
    _ = 0 := by rw [genericUnitDescendant_orthogonal Q Q r s n m hr hr hs hs hne,mul_zero]

theorem pairCoupledWedge_orthogonal (Q r s n m : ℕ) (hr : r ≤ Q) (hs : s ≤ Q)
    (hor : Odd r) (hos : Odd s) (hne : r ≠ s ∨ n ≠ m) :
    (∑ i, pairCoupledWedge Q r hr n i * pairCoupledWedge Q s hs m i) = 0 := by
  rw [pairCoupledWedge,pairCoupledWedge,antisymmetric_pairing Q _ _
    (pairCoupledTensor_antisymmetric Q r n hr hor) (pairCoupledTensor_antisymmetric Q s m hs hos)]
  exact pairCoupledTensor_orthogonal Q r s n m hr hs hne

noncomputable def pairCoupledInclusion (Q r : ℕ) (hr : r ≤ Q) :
    Matrix (WedgePairIndex Q) (Fin (genericCoupledWeight Q Q r+1)) ℝ :=
  fun i n => pairCoupledWedge Q r hr n.val i

theorem pairCoupledInclusion_isometry (Q r : ℕ) (hr : r ≤ Q) (ho : Odd r) :
    (pairCoupledInclusion Q r hr)ᵀ * pairCoupledInclusion Q r hr = 1 := by
  ext n m
  simp only [Matrix.mul_apply,Matrix.transpose_apply,pairCoupledInclusion,Matrix.one_apply]
  by_cases h : n=m
  · subst m
    rw [ite_eq_left rfl]
    simpa only [pow_two,vectorNormSq] using pairCoupledWedge_norm Q r n.val hr ho (by omega)
  · rw [ite_eq_right h]
    exact pairCoupledWedge_orthogonal Q r r n.val m.val hr hr ho ho
      (Or.inr (fun he => h (Fin.ext he)))

end Laughlin.Spin

end OAI
