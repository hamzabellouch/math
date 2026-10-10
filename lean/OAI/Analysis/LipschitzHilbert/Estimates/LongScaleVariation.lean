import OAI.Analysis.LipschitzHilbert.Packets.VariationPacketL1
import OAI.Analysis.LipschitzHilbert.Estimates.GeometricScaleWeights
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! Spatial oscillation of the long-scale partial-sum variation, obtained
from the actual packet derivatives and their geometric scale sum. -/

noncomputable section
open Set
open scoped BigOperators

namespace LipschitzHilbert

theorem packetPartialSum_sub {E : Type*} [AddCommGroup E] {N : ℕ}
    (f g : Fin N → E) (n : ℕ) :
    packetPartialSum f n - packetPartialSum g n = packetPartialSum (fun j => f j - g j) n := by
  unfold packetPartialSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < n <;> simp only [hj, ite_true, ite_false, sub_zero]

theorem long_scale_variation_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (f : Fin N → ℝ → E) (a b : ℝ) (D : Fin N → ℝ)
    (hf : ∀ j x, x ∈ Icc a b → DifferentiableAt ℝ (f j) x)
    (hderiv : ∀ j x, x ∈ Icc a b → ‖deriv (f j) x‖ ≤ D j)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    cubicVariation (fun n => packetPartialSum (fun j => f j x) n -
      packetPartialSum (fun j => f j y) n) N ≤ (∑ j, D j) * |x - y| := by
  simp_rw [packetPartialSum_sub]
  calc
    _ ≤ ∑ j, ‖f j x - f j y‖ := cubicVariation_packetPartialSum_le _
    _ ≤ ∑ j, D j * |x - y| := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Real.norm_eq_abs] using
        (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le (hf j) (hderiv j) hy hx
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem long_dyadic_variation_oscillation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (f : Fin N → ℝ → E) (u r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hf : ∀ j x, x ∈ Icc (u - r) (u + r) → DifferentiableAt ℝ (f j) x)
    (hderiv : ∀ j x, x ∈ Icc (u - r) (u + r) →
      ‖deriv (f j) x‖ ≤ (C / r) * (1 / 2 : ℝ) ^ j.val)
    {x y : ℝ} (hx : x ∈ Icc (u - r) (u + r)) (hy : y ∈ Icc (u - r) (u + r)) :
    cubicVariation (fun n => packetPartialSum (fun j => f j x) n -
      packetPartialSum (fun j => f j y) n) N ≤ 4 * C := by
  have hsum : (∑ j : Fin N, (C / r) * (1 / 2 : ℝ) ^ j.val) ≤ (C / r) * 2 := by
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range]
    exact mul_le_mul_of_nonneg_left (sum_half_powers_le_two N) (div_nonneg hC hr.le)
  have hxy : |x - y| ≤ 2 * r := abs_le.mpr ⟨by linarith [hx.1,hy.2], by linarith [hx.2,hy.1]⟩
  calc
    _ ≤ (∑ j : Fin N, (C / r) * (1 / 2 : ℝ) ^ j.val) * |x - y| :=
      long_scale_variation_lipschitz f _ _ _ hf hderiv hx hy
    _ ≤ ((C / r) * 2) * (2 * r) :=
      mul_le_mul hsum hxy (abs_nonneg _) (by positivity)
    _ = 4 * C := by field_simp; ring

end LipschitzHilbert

end

end OAI
