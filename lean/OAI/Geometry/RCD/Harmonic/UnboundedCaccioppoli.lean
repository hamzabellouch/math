import OAI.Geometry.RCD.Sobolev.CutoffGamma

namespace OAI

/-! # Caccioppoli estimates for unbounded Sobolev functions

The test is the square of a compact Lipschitz cutoff times the function.
The cutoff multiplication operator makes this test admissible without
assuming that the function is bounded.
-/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Right-hand form of the cutoff product rule. -/
theorem localGamma_cutoffCLM_right (f η h : SobolevSpace μ hQ)
    {v : X → ℝ} {L B : ℝ≥0} (hv : LipschitzWith L v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] v) :
    localGamma μ hQ h (SobolevSpace.cutoffCLM μ hQ hv hs hb hn f) =ᵐ[μ]
      fun x => v x*localGamma μ hQ h f x+
        SobolevSpace.toLp μ hQ f x*localGamma μ hQ h η x := by
  filter_upwards [localGamma_comm μ hQ h (SobolevSpace.cutoffCLM μ hQ hv hs hb hn f),
    localGamma_cutoffCLM μ hQ f η h hv hs hb hn hrep,
    localGamma_comm μ hQ f h,localGamma_comm μ hQ η h] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]

/-- The Caccioppoli bound requires a bounded cutoff gradient, but no bound
on the function tested. -/
theorem caccioppoli_cutoffCLM_energy (u η : SobolevSpace μ hQ)
    {v : X → ℝ} {L B A : ℝ≥0} (hv : LipschitzWith L v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] v)
    (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ A) :
    (∫ x, (SobolevSpace.toLp μ hQ η x)^2*(SobolevSpace.minimalSlope μ hQ u x)^2 ∂μ) ≤
      2*energyForm μ hQ u (SobolevSpace.cutoffCLM μ hQ hv hs hb hn
        (SobolevSpace.cutoffCLM μ hQ hv hs hb hn u))+
      4*∫ x, (SobolevSpace.toLp μ hQ u x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ := by
  let M := SobolevSpace.cutoffCLM μ hQ hv hs hb hn
  have hη : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ B := by
    filter_upwards [hrep] with x hx
    rw [hx]
    exact hb x
  have hform : localGamma μ hQ u (M (M u)) =ᵐ[μ] fun x =>
      (SobolevSpace.toLp μ hQ η x)^2*(SobolevSpace.minimalSlope μ hQ u x)^2+
      2*SobolevSpace.toLp μ hQ η x*SobolevSpace.toLp μ hQ u x*
        localGamma μ hQ u η x := by
    filter_upwards [localGamma_cutoffCLM_right μ hQ (M u) η u hv hs hb hn hrep,
      localGamma_cutoffCLM_right μ hQ u η u hv hs hb hn hrep,
      SobolevSpace.cutoffCLM_coe μ hQ hv hs hb hn u,
      localGamma_self μ hQ u,hrep] with x h1 h2 h3 h4 hr
    change localGamma μ hQ u (M (M u)) x = _ at h1
    change localGamma μ hQ u (M u) x = _ at h2
    change SobolevSpace.toLp μ hQ (M u) x = _ at h3
    rw [h1,h2,h3,h4,← hr]
    ring
  have hi1 := bounded_square_weight_integrable μ (SobolevSpace.toLp μ hQ η)
    (SobolevSpace.minimalSlope μ hQ u) hη
  have hi2 : Integrable (fun x => (SobolevSpace.toLp μ hQ u x)^2*
      (SobolevSpace.minimalSlope μ hQ η x)^2) μ := by
    exact (bounded_square_weight_integrable μ (SobolevSpace.minimalSlope μ hQ η)
      (SobolevSpace.toLp μ hQ u) hgrad).congr (Eventually.of_forall fun x => mul_comm _ _)
  have hx : (∫ x, (SobolevSpace.toLp μ hQ η x)^2*
      (SobolevSpace.minimalSlope μ hQ u x)^2 ∂μ) ≤
      ∫ x, 2*localGamma μ hQ u (M (M u)) x+
        4*((SobolevSpace.toLp μ hQ u x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2) ∂μ := by
    apply integral_mono_ae hi1
      ((localGamma_memL1 μ hQ u (M (M u))).const_mul 2 |>.add (hi2.const_mul 4))
    filter_upwards [hform,localGamma_abs_le μ hQ u η,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ u),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ η)] with x hf hγ hu hη
    change _ ≤ 2*localGamma μ hQ u (M (M u)) x+
      4*((SobolevSpace.toLp μ hQ u x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2)
    rw [hf]
    simpa only [mul_assoc] using caccioppoli_scalar hu hη hγ
  rw [integral_add ((localGamma_memL1 μ hQ u (M (M u))).const_mul 2) (hi2.const_mul 4),
    integral_const_mul,integral_const_mul,integral_localGamma_eq_energyForm] at hx
  exact hx

/-- The zero-source specialization used in harmonic level-set iteration. -/
theorem caccioppoli_cutoffCLM (u η : SobolevSpace μ hQ)
    {v : X → ℝ} {L B A : ℝ≥0} (hv : LipschitzWith L v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] v)
    (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ A)
    (hzero : energyForm μ hQ u (SobolevSpace.cutoffCLM μ hQ hv hs hb hn
      (SobolevSpace.cutoffCLM μ hQ hv hs hb hn u)) = 0) :
    (∫ x, (SobolevSpace.toLp μ hQ η x)^2*(SobolevSpace.minimalSlope μ hQ u x)^2 ∂μ) ≤
      4*∫ x, (SobolevSpace.toLp μ hQ u x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ := by
  simpa only [hzero,mul_zero,zero_add] using
    caccioppoli_cutoffCLM_energy μ hQ u η hv hs hb hn hrep hgrad

end RegularPointCoordinates

end

end OAI
