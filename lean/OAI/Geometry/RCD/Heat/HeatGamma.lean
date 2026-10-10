import OAI.Geometry.RCD.Heat.HeatGammaSobolev

namespace OAI

/-! # The energy density of an actual heat solution is Sobolev

The weak Bochner inequality is tested against heat regularizations of the
same nonnegative energy density. Its bounded amplitude controls the mixed
term uniformly as the regularization time tends to zero.
-/

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_gamma_finite_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) {t : ℝ} (ht : 0 < t)
    (H : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hH : (fun x => (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic t ht f) x) ^ 2) =ᵐ[hausdorff n X] H)
    (hHC : ∀ᵐ x ∂hausdorff n X, |H x| ≤ C) :
    energyLp (hausdorff n X) H ≠ ∞ := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let F := heatSobolev μ hX.quadratic t ht f
  let D := heatSobolevMap μ hX.quadratic (t / 2) (half_pos ht)
    (-heatGeneratorAt μ hX.quadratic (t - t / 2) f)
  have hH0 : 0 ≤ H := by
    apply (Lp.coeFn_nonneg H).mp
    filter_upwards [hH] with x hx
    rw [← hx]
    positivity
  let B := 2 * |K| * ‖H‖ ^ 2 + 2 * (C : ℝ) * ‖F‖ * ‖D‖
  have hE (s : ℝ) (hs : 0 < s) :
      energyForm μ hX.quadratic (heatSobolev μ hX.quadratic s hs H)
        (heatSobolev μ hX.quadratic s hs H) ≤ B := by
    let W := heatAt μ hX.quadratic (2 * s) H
    have hWC : ∀ᵐ x ∂μ, |W x| ≤ C :=
      heatAt_abs_le_const μ hX.quadratic (2 * s) C H hHC
    have hWnorm : ∀ᵐ x ∂μ, ‖W x‖ ≤ (C : ℝ) := by
      simpa only [Real.norm_eq_abs] using hWC
    have hboch := hX.heat_weak_bochner K n hn p f H hH0 C hHC t (2 * s) ht (by positivity) H hH
    change K * (∫ x, W x * (SobolevSpace.minimalSlope μ hX.quadratic F x) ^ 2 ∂μ) +
      weightedGamma μ hX.quadratic W F D ≤
        (1 / 2 : ℝ) * ∫ x, (-heatGeneratorAt μ hX.quadratic (2 * s) H) x * H x ∂μ at hboch
    have hI : (∫ x, W x * (SobolevSpace.minimalSlope μ hX.quadratic F x) ^ 2 ∂μ) =
        inner ℝ W H := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hH] with x hx
      simp only [Real.inner_apply, ← hx]
      ring
    have hJ : (∫ x, (-heatGeneratorAt μ hX.quadratic (2 * s) H) x * H x ∂μ) =
        -energyForm μ hX.quadratic (heatSobolev μ hX.quadratic s hs H)
          (heatSobolev μ hX.quadratic s hs H) := by
      have hi : (∫ x, (-heatGeneratorAt μ hX.quadratic (2 * s) H) x * H x ∂μ) =
          inner ℝ (-heatGeneratorAt μ hX.quadratic (2 * s) H) H := by
        simp only [L2.inner_def, Real.inner_apply, mul_comm]
      rw [hi, heatGeneratorAt_of_pos μ hX.quadratic (2 * s) (by positivity),
        inner_neg_left, heatGenerator_inner]
      congr 2 <;> congr 1 <;> ring
    rw [hI, hJ] at hboch
    have hW : ‖W‖ ≤ ‖H‖ := by
      simpa only [one_mul] using (heatAt μ hX.quadratic (2 * s)).le_of_opNorm_le (heatAt_norm_le μ hX.quadratic _) H
    have hpair : |inner ℝ W H| ≤ ‖H‖ ^ 2 := by
      calc
        _ ≤ ‖W‖ * ‖H‖ := by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) W H
        _ ≤ ‖H‖ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hW (norm_nonneg H)]
    have hKi : -(|K| * ‖H‖ ^ 2) ≤ K * inner ℝ W H := by
      have hh : |K * inner ℝ W H| ≤ |K| * ‖H‖ ^ 2 := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hpair (abs_nonneg K)
      exact (neg_le_neg hh).trans (neg_abs_le _)
    have hG := weightedGamma_norm_le μ hX.quadratic hWnorm F D
    have hGlo : -((C : ℝ) * ‖F‖ * ‖D‖) ≤ weightedGamma μ hX.quadratic W F D := by
      have hh : |weightedGamma μ hX.quadratic W F D| ≤ (C : ℝ) * ‖F‖ * ‖D‖ := by
        simpa only [Real.norm_eq_abs] using hG
      exact (neg_le_neg hh).trans (neg_abs_le _)
    dsimp only [B]
    linarith
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (energyLp_le_of_heat_energy_bound μ hX.quadratic H B hE)

end RegularPointCoordinates

end

end OAI
