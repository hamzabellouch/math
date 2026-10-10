import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
An affine map controlled at a base point and its basis anchors is controlled at every affine
combination by the sum of the absolute coordinates. The operator norm of the basis-coordinate
map bounds that sum in terms of the dimension and the ambient norm on the subspace.
-/

namespace RieszRectifiability

noncomputable section

open Module
open scoped BigOperators

theorem affine_map_norm_bound_from_anchors {n d q : ℕ}
    (c : Ambient q) (B : Ambient d →L[ℝ] Ambient q) (a : Ambient d)
    (v : Fin n → Ambient d) (t : Fin n → ℝ) (ε : ℝ)
    (hbase : ‖c + B a‖ ≤ ε) (hvertices : ∀ i, ‖c + B (a + v i)‖ ≤ ε) :
    ‖c + B (a + ∑ i, t i • v i)‖ ≤ ε * (1 + 2 * ∑ i, |t i|) := by
  have hv : ∀ i, ‖B (v i)‖ ≤ 2 * ε := by
    intro i
    calc
      _ = ‖(c + B (a + v i)) - (c + B a)‖ := by rw [map_add]; congr 1; abel
      _ ≤ ‖c + B (a + v i)‖ + ‖c + B a‖ := norm_sub_le _ _
      _ ≤ 2 * ε := by linarith [hvertices i]
  calc
    _ = ‖(c + B a) + ∑ i, t i • B (v i)‖ := by
      simp only [map_add, map_sum, map_smul, add_assoc]
    _ ≤ ‖c + B a‖ + ‖∑ i, t i • B (v i)‖ := norm_add_le _ _
    _ ≤ ε + ∑ i, ‖t i • B (v i)‖ :=
      add_le_add hbase (norm_sum_le _ _)
    _ ≤ ε + ∑ i, |t i| * (2 * ε) := by
      apply add_le_add (le_refl ε)
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

def basisCoordinateNorm {n d : ℕ} {S : Submodule ℝ (Ambient d)}
    (b : Basis (Fin n) ℝ S) : ℝ := by
  let : ContinuousSMul ℝ S := IsBoundedSMul.continuousSMul
  exact ‖b.equivFun.toContinuousLinearEquiv.toContinuousLinearMap‖

theorem basisCoordinateNorm_nonneg {n d : ℕ} {S : Submodule ℝ (Ambient d)}
    (b : Basis (Fin n) ℝ S) : 0 ≤ basisCoordinateNorm b := by
  let : ContinuousSMul ℝ S := IsBoundedSMul.continuousSMul
  unfold basisCoordinateNorm
  exact norm_nonneg b.equivFun.toContinuousLinearEquiv.toContinuousLinearMap

theorem basis_coordinate_l1_bound {n d : ℕ} {S : Submodule ℝ (Ambient d)}
    (b : Basis (Fin n) ℝ S) (u : S) :
    (∑ i, |b.equivFun u i|) ≤ (n : ℝ) * basisCoordinateNorm b * ‖u‖ := by
  let : ContinuousSMul ℝ S := IsBoundedSMul.continuousSMul
  have hnorm : ‖b.equivFun u‖ ≤ basisCoordinateNorm b * ‖u‖ :=
    b.equivFun.toContinuousLinearEquiv.toContinuousLinearMap.le_opNorm u
  calc
    _ ≤ ∑ _i : Fin n, ‖b.equivFun u‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using! norm_le_pi_norm (b.equivFun u) i
    _ = (n : ℝ) * ‖b.equivFun u‖ := by simp
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      simpa only [mul_assoc] using! h

end

end RieszRectifiability

end OAI
