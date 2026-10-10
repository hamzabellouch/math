import OAI.Analysis.CircleDomains.Sobolev.ScalarWeakLimits
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! Compact planar tests are legitimate dual tests for spherical L² after
dividing by the explicit positive stereographic area density. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def weightedScalarTest (ψ : ℂ → ℝ) (z : ℂ) : ℝ := ψ z / sphericalAreaDensity z

 theorem weightedScalarTest_continuous {ψ : ℂ → ℝ} (hψ : Continuous ψ) :
    Continuous (weightedScalarTest ψ) :=
  hψ.div continuous_sphericalAreaDensity (fun z => (sphericalAreaDensity_pos z).ne')

 theorem weightedScalarTest_compact {ψ : ℂ → ℝ} (hs : HasCompactSupport ψ) :
    HasCompactSupport (weightedScalarTest ψ) := by
  change HasCompactSupport (fun z => ψ z * (sphericalAreaDensity z)⁻¹)
  exact hs.mul_right

 theorem weightedScalarTest_memLp {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    MemLp (weightedScalarTest ψ) 2 planarSphericalArea :=
  (weightedScalarTest_continuous hψ).memLp_of_hasCompactSupport (weightedScalarTest_compact hs)

 theorem integral_weightedScalarTest (u ψ : ℂ → ℝ) :
    (∫ z, u z * weightedScalarTest ψ z ∂planarSphericalArea) = ∫ z, u z * ψ z := by
  rw [planarSphericalArea, integral_withDensity_eq_integral_toReal_smul
    continuous_sphericalAreaDensity.measurable.ennreal_ofReal
    (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    change (ENNReal.ofReal (sphericalAreaDensity z)).toReal *
      (u z * weightedScalarTest ψ z) = u z * ψ z
    rw [ENNReal.toReal_ofReal (sphericalAreaDensity_pos z).le]
    unfold weightedScalarTest
    field_simp [(sphericalAreaDensity_pos z).ne']

 theorem tendsto_pairings_with_memLp_test
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {u : ℕ → X → ℝ} {V : X → ℝ}
    (hlim : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, u n x * w x ∂μ)
      atTop (𝓝 (∫ x, V x * w x ∂μ))) {ψ : X → ℝ} (hψ : MemLp ψ 2 μ) :
    Tendsto (fun n => ∫ x, u n x * ψ x ∂μ) atTop (𝓝 (∫ x, V x * ψ x ∂μ)) := by
  have he (f : X → ℝ) : (∫ x, f x * hψ.toLp ψ x ∂μ) = ∫ x, f x * ψ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp] with x hx
    rw [hx]
  simpa only [he] using hlim (hψ.toLp ψ)

 theorem tendsto_planar_pairings_of_spherical
    {u : ℕ → ℂ → ℝ} {V : ℂ → ℝ}
    (hlim : ∀ w : Lp ℝ 2 planarSphericalArea,
      Tendsto (fun n => ∫ z, u n z * w z ∂planarSphericalArea)
        atTop (𝓝 (∫ z, V z * w z ∂planarSphericalArea)))
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ z, u n z * ψ z) atTop (𝓝 (∫ z, V z * ψ z)) := by
  have h := tendsto_pairings_with_memLp_test hlim (weightedScalarTest_memLp hψ hs)
  simpa only [integral_weightedScalarTest] using h

end CircleDomainRigidity

end

end OAI
