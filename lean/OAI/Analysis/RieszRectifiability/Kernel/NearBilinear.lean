import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NearPairWeight
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalBilinear

namespace OAI

/-!
# Near-diagonal fractional bilinear bounds

On the near-pair region, Lipschitz control makes the test function's fractional energy
integrable under upper growth. Cauchy–Schwarz then bounds the absolute bilinear pairing
by the full energy of the other function and the near-pair inverse-distance integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem near_fractionalBilinear_integrable_and_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w ψ : Ambient d → ℝ) (hw : Measurable w) (L : ℝ≥0) (hψ : LipschitzWith L ψ)
    (henergy : Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) w q.1 q.2) (μ.prod μ))
    (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) w ψ q.1 q.2)
      (nearPairSet r) (μ.prod μ) ∧
      (∫ q in nearPairSet r, |fractionalBilinear (p + 1) w ψ q.1 q.2| ∂μ.prod μ) ^ 2 ≤
        (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) w q.1 q.2 ∂μ.prod μ) *
          ((L : ℝ) ^ 2 * (μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)))) := by
  let ρ : Measure (Ambient d × Ambient d) := (μ.prod μ).restrict (nearPairSet r)
  have hweak : Integrable (fun q : Ambient d × Ambient d => inverseDistancePow p q.1 q.2) ρ :=
    (integrable_indicator_iff (nearPairSet_measurable r)).mp
      (nearPairWeight_integrable p C μ hg r hr)
  have htestMeas : AEStronglyMeasurable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) ψ q.1 q.2) ρ := by
    have hψm : Measurable ψ := hψ.continuous.measurable
    apply Measurable.aestronglyMeasurable
    unfold fractionalPairEnergy
    fun_prop
  have htestEnergy : Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) ψ q.1 q.2) ρ := by
    apply (hweak.const_mul ((L : ℝ) ^ 2)).mono' htestMeas
    apply Filter.Eventually.of_forall
    intro q
    rw [Real.norm_of_nonneg (fractionalPairEnergy_nonneg _ _ _ _)]
    exact lipschitz_fractionalEnergy_bound p ψ L hψ q.1 q.2
  have hf := weightedDifference_memLp (p + 1) w hw ρ henergy.restrict
  have hgtest := weightedDifference_memLp (p + 1) ψ hψ.continuous.measurable ρ htestEnergy
  have hprod : MemLp (fun q : Ambient d × Ambient d =>
      weightedDifference (p + 1) w q.1 q.2 * weightedDifference (p + 1) ψ q.1 q.2) 1 ρ :=
    hf.mul hgtest
  have hcs := integral_mul_cauchy_schwarz_sq ρ
    (fun q => ‖weightedDifference (p + 1) w q.1 q.2‖)
    (fun q => ‖weightedDifference (p + 1) ψ q.1 q.2‖) hf.norm hgtest.norm
  simp only [Real.norm_eq_abs, ← abs_mul, weightedDifference_mul, sq_abs,
    weightedDifference_sq] at hcs
  have hwork : (∫ q, fractionalPairEnergy (p + 1) w q.1 q.2 ∂ρ) ≤
      ∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) w q.1 q.2 ∂μ.prod μ :=
    setIntegral_le_integral henergy
      (Filter.Eventually.of_forall fun q => fractionalPairEnergy_nonneg _ _ _ _)
  have hweakBound : (∫ q, inverseDistancePow p q.1 q.2 ∂ρ) ≤
      μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) := by
    change (∫ q in nearPairSet r, inverseDistancePow p q.1 q.2 ∂μ.prod μ) ≤ _
    rw [← integral_indicator (nearPairSet_measurable r)]
    exact nearPairWeight_integral_bound p C μ hg r hr
  have htestBound : (∫ q, fractionalPairEnergy (p + 1) ψ q.1 q.2 ∂ρ) ≤
      (L : ℝ) ^ 2 * (μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))) := by
    have h := integral_mono htestEnergy (hweak.const_mul ((L : ℝ) ^ 2))
      (fun q => lipschitz_fractionalEnergy_bound p ψ L hψ q.1 q.2)
    rw [integral_const_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hweakBound (sq_nonneg _))
  refine ⟨?_, ?_⟩
  · simpa only [weightedDifference_mul] using! memLp_one_iff_integrable.mp hprod
  · exact hcs.trans (mul_le_mul hwork htestBound
      (integral_nonneg (fun q => fractionalPairEnergy_nonneg _ _ _ _))
      (integral_nonneg (fun q => fractionalPairEnergy_nonneg _ _ _ _)))

theorem near_fractionalBilinear_absolute_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w ψ : Ambient d → ℝ) (hw : Measurable w) (L : ℝ≥0) (hψ : LipschitzWith L ψ)
    (henergy : Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) w q.1 q.2) (μ.prod μ))
    (r : ℝ) (hr : 0 < r) :
    (∫ q in nearPairSet r, |fractionalBilinear (p + 1) w ψ q.1 q.2| ∂μ.prod μ) ≤
      Real.sqrt ((∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) w q.1 q.2 ∂μ.prod μ) *
          ((L : ℝ) ^ 2 * (μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))))) := by
  have h := Real.sqrt_le_sqrt
    (near_fractionalBilinear_integrable_and_bound p C μ hg w ψ hw L hψ henergy r hr).2
  simpa only [Real.sqrt_sq (integral_nonneg (fun q => abs_nonneg _))] using! h

end

end RieszRectifiability

end OAI
