import OAI.Geometry.RCD.Sobolev.CutoffProductEnergy
import OAI.Geometry.RCD.Metric.L2LevelMeasure

namespace OAI

/-! # Localization of cutoff L² and gradient terms -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
/-- A cutoff supported in a measurable set localizes its multiplier norm. -/
theorem cutoffCLM_norm_sq_le_setIntegral (u : SobolevSpace μ hQ)
    {v : X → ℝ} {L B : ℝ≥0} (hv : LipschitzWith L v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    {Ω : Set X} (hΩ : MeasurableSet Ω) (hsΩ : tsupport v ⊆ Ω) :
    ‖SobolevSpace.toLp μ hQ (SobolevSpace.cutoffCLM μ hQ hv hs hb hn u)‖^2 ≤
      (B:ℝ)^2*∫ x in Ω, (SobolevSpace.toLp μ hQ u x)^2 ∂μ := by
  classical
  let U := SobolevSpace.toLp μ hQ u
  let z := SobolevSpace.cutoffCLM μ hQ hv hs hb hn u
  have hi : Integrable (fun x => (B:ℝ)^2*U x^2) μ := (Lp.memLp U).integrable_sq.const_mul _
  rw [← lp_integral_square_eq_norm_square]
  calc
    _ ≤ ∫ x, Ω.indicator (fun x => (B:ℝ)^2*U x^2) x ∂μ := by
      apply integral_mono_ae (Lp.memLp (SobolevSpace.toLp μ hQ z)).integrable_sq
        (hi.indicator hΩ)
      filter_upwards [SobolevSpace.cutoffCLM_coe μ hQ hv hs hb hn u] with x hx
      change SobolevSpace.toLp μ hQ z x = v x*U x at hx
      change (SobolevSpace.toLp μ hQ z x)^2 ≤ _
      rw [hx]
      by_cases hxΩ : x ∈ Ω
      · rw [indicator_of_mem hxΩ,mul_pow]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v x)) B.coe_nonneg).mpr (hb x))
          (sq_nonneg (U x))
      · rw [indicator_of_notMem hxΩ,
          image_eq_zero_of_notMem_tsupport (fun ht => hxΩ (hsΩ ht)),zero_mul,zero_pow (by decide)]
    _ = _ := by rw [integral_indicator hΩ,integral_const_mul]

/-- Locality makes the gradient-weighted L² error vanish outside the
support of the cutoff. -/
theorem cutoff_gradient_weight_le_setIntegral (u η : SobolevSpace μ hQ)
    {v : X → ℝ} (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] v)
    {A : ℝ≥0} (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ A)
    {Ω : Set X} (hΩ : MeasurableSet Ω) (hsΩ : tsupport v ⊆ Ω) :
    (∫ x, (SobolevSpace.toLp μ hQ u x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ) ≤
      (A:ℝ)^2*∫ x in Ω, (SobolevSpace.toLp μ hQ u x)^2 ∂μ := by
  classical
  let U := SobolevSpace.toLp μ hQ u
  have hi : Integrable (fun x => U x^2*(SobolevSpace.minimalSlope μ hQ η x)^2) μ :=
    (bounded_square_weight_integrable μ (SobolevSpace.minimalSlope μ hQ η) U hgrad).congr
      (Eventually.of_forall fun x => mul_comm _ _)
  have hj : Integrable (fun x => (A:ℝ)^2*U x^2) μ := (Lp.memLp U).integrable_sq.const_mul _
  calc
    _ ≤ ∫ x, Ω.indicator (fun x => (A:ℝ)^2*U x^2) x ∂μ := by
      apply integral_mono_ae hi (hj.indicator hΩ)
      filter_upwards [hrep,hgrad,SobolevSpace.minimalSlope_zero_on_level μ hQ η 0] with x hr hg hz
      by_cases hxΩ : x ∈ Ω
      · rw [indicator_of_mem hxΩ,mul_comm ((A:ℝ)^2)]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) A.coe_nonneg).mpr hg)
          (sq_nonneg (U x))
      · have hv0 : v x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hxΩ (hsΩ ht))
        rw [indicator_of_notMem hxΩ,hz (hr.trans hv0),zero_pow (by decide),mul_zero]
    _ = _ := by rw [integral_indicator hΩ,integral_const_mul]

end RegularPointCoordinates

end

end OAI
