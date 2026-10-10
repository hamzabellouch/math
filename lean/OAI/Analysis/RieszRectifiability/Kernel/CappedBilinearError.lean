import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CappedBilinearConvergence
import OAI.Analysis.RieszRectifiability.Kernel.UniformNearBilinear

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem capped_bilinear_error_pointwise {d : ℕ} (m : ℕ) (ε : ℝ)
    (w φ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    |fractionalBilinear m w φ q.1 q.2 - (w q.1 - w q.2) * cappedTestKernel m ε φ q| ≤
      (nearPairSet ε).indicator (fun q => |fractionalBilinear m w φ q.1 q.2|) q := by
  classical
  by_cases hnear : q ∈ nearPairSet ε
  · rw [indicator_of_mem hnear]
    by_cases hdiag : q.1 = q.2
    · simp only [hdiag, fractionalBilinear, cappedTestKernel, sub_self, zero_mul, zero_div,
        abs_zero, le_refl]
    · have hd : 0 < dist q.1 q.2 := dist_pos.mpr hdiag
      have hcap : cappedInverseDistancePow (m + 1) ε q ≤ (dist q.1 q.2 ^ (m + 1))⁻¹ := by
        exact inv_anti₀ (pow_pos hd _) (pow_le_pow_left₀ hd.le (le_max_right _ _) _)
      have hdiff : 0 ≤ (dist q.1 q.2 ^ (m + 1))⁻¹ - cappedInverseDistancePow (m + 1) ε q :=
        sub_nonneg.mpr hcap
      have heq : fractionalBilinear m w φ q.1 q.2 - (w q.1 - w q.2) * cappedTestKernel m ε φ q =
          ((w q.1 - w q.2) * (φ q.1 - φ q.2)) *
            ((dist q.1 q.2 ^ (m + 1))⁻¹ - cappedInverseDistancePow (m + 1) ε q) := by
        unfold fractionalBilinear cappedTestKernel
        ring
      rw [heq, abs_mul, abs_of_nonneg hdiff]
      calc
        _ ≤ |(w q.1 - w q.2) * (φ q.1 - φ q.2)| * (dist q.1 q.2 ^ (m + 1))⁻¹ := by
          exact mul_le_mul_of_nonneg_left
            (sub_le_self _ (cappedInverseDistancePow_nonneg (m + 1) ε q)) (abs_nonneg _)
        _ = _ := by
          simp only [fractionalBilinear, div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hd _))]
  · rw [indicator_of_notMem hnear]
    have hd : ε ≤ dist q.1 q.2 := by
      have hn : ¬dist q.2 q.1 ≤ ε := hnear
      simpa only [dist_comm q.2 q.1] using! (lt_of_not_ge hn).le
    rw [capped_bilinear_eq_outside m ε w φ q hd, sub_self, abs_zero]

theorem fractional_bilinear_integrable_and_cap_error {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w φ : Ambient d → ℝ) (hw : Measurable w) (hwI : Integrable w μ)
    (L B : ℝ≥0) (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (henergy : Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) w q.1 q.2) (μ.prod μ))
    (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) w φ q.1 q.2) (μ.prod μ) ∧
      |(∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) w φ q.1 q.2 ∂μ.prod μ) -
        ∫ q : Ambient d × Ambient d, (w q.1 - w q.2) * cappedTestKernel (p + 1) ε φ q ∂μ.prod μ| ≤
          ∫ q in nearPairSet ε, |fractionalBilinear (p + 1) w φ q.1 q.2| ∂μ.prod μ := by
  let F := fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) w φ q.1 q.2
  let G := fun q : Ambient d × Ambient d => (w q.1 - w q.2) * cappedTestKernel (p + 1) ε φ q
  have hFmeas : Measurable F := by
    dsimp only [F]
    unfold fractionalBilinear
    have hφm := hφ.continuous.measurable
    fun_prop
  have hGkernel := cappedTestKernel_lipschitz (p + 1) ε hε φ L B hφ hB
  have hG : Integrable G (μ.prod μ) :=
    (antisymmetric_kernel_pairing μ w hwI (cappedTestKernel (p + 1) ε φ)
      hGkernel.continuous.measurable ((2 * (B : ℝ)) * (ε ^ (p + 1 + 1))⁻¹)
      (cappedTestKernel_bound (p + 1) ε hε φ B hB) (cappedTestKernel_antisymm (p + 1) ε φ)).1
  have hnear : IntegrableOn F (nearPairSet ε) (μ.prod μ) :=
    (near_fractionalBilinear_integrable_and_bound p C μ hg w φ hw L hφ henergy ε hε).1
  have hdom : Integrable ((nearPairSet ε).indicator (fun q => |F q|)) (μ.prod μ) :=
    (integrable_indicator_iff (nearPairSet_measurable ε)).mpr hnear.abs
  have herr : Integrable (fun q => F q - G q) (μ.prod μ) := by
    apply hdom.mono' (hFmeas.aestronglyMeasurable.sub hG.aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro q
    simpa only [Real.norm_eq_abs] using! capped_bilinear_error_pointwise (p + 1) ε w φ q
  have hF : Integrable F (μ.prod μ) := by
    have heq : F = fun q => (F q - G q) + G q := by funext q; ring
    rw [heq]
    exact herr.add hG
  refine ⟨hF, ?_⟩
  change |(∫ q, F q ∂μ.prod μ) - ∫ q, G q ∂μ.prod μ| ≤ ∫ q in nearPairSet ε, |F q| ∂μ.prod μ
  rw [← integral_sub hF hG, ← integral_indicator (nearPairSet_measurable ε)]
  calc
    _ ≤ ∫ q, |F q - G q| ∂μ.prod μ := abs_integral_le_integral_abs
    _ ≤ _ := integral_mono_ae herr.abs hdom
      (Filter.Eventually.of_forall fun q => capped_bilinear_error_pointwise (p + 1) ε w φ q)

end

end RieszRectifiability

end OAI
