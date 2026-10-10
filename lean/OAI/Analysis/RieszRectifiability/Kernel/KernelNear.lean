import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.InnerAnnuli

namespace OAI

/-!
# Near-field inverse-distance estimates

Inner dyadic annuli turn upper growth of order `p + 1` into a summable bound for
the inverse-distance power of order `p`. The center has zero measure, so the
annular estimates give integrability and a quantitative bound on the closed ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped ENNReal

theorem dyadic_near_coefficient (p k : ℕ) (C r : ℝ) (hr : 0 < r) :
    ((r * (1 / 2 : ℝ) ^ (k + 1)) ^ p)⁻¹ *
      (C * (2 * (r * (1 / 2 : ℝ) ^ k)) ^ (p + 1)) =
      (C * 2 ^ (p + 1) * 2 ^ p * r) * (1 / 2 : ℝ) ^ k := by
  let b : ℝ := r * (1 / 2 : ℝ) ^ k
  have hb : b ≠ 0 := by dsimp [b]; positivity
  have hs : r * (1 / 2 : ℝ) ^ (k + 1) = b / 2 := by
    dsimp [b]
    rw [pow_succ]
    ring
  calc
    _ = (C * 2 ^ (p + 1) * 2 ^ p) * b := by
      rw [hs]
      change ((b / 2) ^ p)⁻¹ * (C * (2 * b) ^ (p + 1)) = _
      rw [div_pow, mul_pow 2 b (p + 1), inv_div, pow_succ b]
      field_simp
    _ = _ := by dsimp [b]; ring

theorem inverseDistancePow_inner_annular_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (x : Ambient d) (r : ℝ) (hr : 0 < r) (k : ℕ) :
    (∫ y in innerDyadicAnnulus x r k, ‖inverseDistancePow p x y‖ ∂μ) ≤
      (C * 2 ^ (p + 1) * 2 ^ p * r) * (1 / 2 : ℝ) ^ k := by
  have hfinite : μ (innerDyadicAnnulus x r k) < ∞ :=
    ((measure_mono (innerDyadicAnnulus_subset_ball x r hr k)).trans
      (hg.2 x _ (by positivity))).trans_lt ENNReal.ofReal_lt_top
  have hmeasure : μ.real (innerDyadicAnnulus x r k) ≤
      C * (2 * (r * (1 / 2 : ℝ) ^ k)) ^ (p + 1) :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity))
      ((measure_mono (innerDyadicAnnulus_subset_ball x r hr k)).trans
        (hg.2 x _ (by positivity)))
  calc
    _ = ‖∫ y in innerDyadicAnnulus x r k, ‖inverseDistancePow p x y‖ ∂μ‖ :=
      (Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)).symm
    _ ≤ ((r * (1 / 2 : ℝ) ^ (k + 1)) ^ p)⁻¹ * μ.real (innerDyadicAnnulus x r k) :=
      norm_setIntegral_le_of_norm_le_const hfinite fun y hy => by
        rw [norm_norm]
        exact inverseDistancePow_bound_on_innerAnnulus p x r hr k y hy
    _ ≤ ((r * (1 / 2 : ℝ) ^ (k + 1)) ^ p)⁻¹ *
        (C * (2 * (r * (1 / 2 : ℝ) ^ k)) ^ (p + 1)) :=
      mul_le_mul_of_nonneg_left hmeasure (by positivity)
    _ = _ := dyadic_near_coefficient p k C r hr

theorem inverseDistancePow_near_integrable_and_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (x : Ambient d) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (inverseDistancePow p x) (closedBall x r) μ ∧
      (∫ y in closedBall x r, ‖inverseDistancePow p x y‖ ∂μ) ≤
        2 * (C * 2 ^ (p + 1) * 2 ^ p * r) := by
  have hgeo : Summable (fun k : ℕ => (C * 2 ^ (p + 1) * 2 ^ p * r) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hs : Summable (fun k : ℕ =>
      ∫ y in innerDyadicAnnulus x r k, ‖inverseDistancePow p x y‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun k => inverseDistancePow_inner_annular_bound p C μ hg x r hr k) hgeo
  have hiu : IntegrableOn (inverseDistancePow p x) (⋃ k, innerDyadicAnnulus x r k) μ :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun k => inverseDistancePow_integrableOn_innerAnnulus (p + 1) p C μ hg x r hr k) hs
  have heq : (⋃ k, innerDyadicAnnulus x r k) =ᵐ[μ] closedBall x r := by
    rw [iUnion_innerDyadicAnnulus x r hr]
    exact sdiff_ae_eq_self.mpr
      (measure_mono_null inter_subset_right (singleton_null_of_globalGrowth p C μ hg x))
  refine ⟨(integrableOn_congr_set_ae heq).mp hiu, ?_⟩
  rw [← Measure.restrict_congr_set heq,
    integral_iUnion (innerDyadicAnnulus_measurable x r) (innerDyadicAnnulus_disjoint x r hr) hiu.norm]
  calc
    _ ≤ ∑' k : ℕ, (C * 2 ^ (p + 1) * 2 ^ p * r) * (1 / 2 : ℝ) ^ k :=
      Summable.tsum_le_tsum (fun k => inverseDistancePow_inner_annular_bound p C μ hg x r hr k)
        hs hgeo
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      norm_num
      ring

theorem inverseDistancePow_near_integral_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (x : Ambient d) (r : ℝ) (hr : 0 < r) :
    (∫ y in closedBall x r, inverseDistancePow p x y ∂μ) ≤
      2 * (C * 2 ^ (p + 1) * 2 ^ p * r) := by
  simpa only [Real.norm_of_nonneg (inverseDistancePow_nonneg p x _)] using!
    (inverseDistancePow_near_integrable_and_bound p C μ hg x r hr).2

end

end RieszRectifiability

end OAI
