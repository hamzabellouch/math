import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OAI.Geometry.NodalSets.Charts.SphereReferenceMeasurePositive

namespace OAI

namespace Yau.Target
open MeasureTheory
open scoped ENNReal
noncomputable section
local instance sphereWeightedL2Measurable : MeasurableSpace Base := borel Base
local instance sphereWeightedL2Borel : BorelSpace Base := ⟨rfl⟩

def sphereWeightedMeasure (rho : Base → ℝ) : Measure Base :=
  sphereReferenceMeasure.withDensity (fun x ↦ ENNReal.ofReal (rho x))

theorem sphereWeightedMeasure_finite (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) : IsFiniteMeasure (sphereWeightedMeasure rho) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal
    (sphereReferenceMeasure_integrable_continuous rho hr) (Filter.Eventually.of_forall hp)]
  exact ENNReal.ofReal_ne_top

theorem sphereWeightedMeasure_integral (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) (f : Base → ℝ) :
    (∫ x, f x ∂sphereWeightedMeasure rho) = ∫ x, rho x*f x ∂sphereReferenceMeasure := by
  rw [sphereWeightedMeasure,integral_withDensity_eq_integral_toReal_smul
    hr.measurable.ennreal_ofReal (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hp _),smul_eq_mul]

theorem sphereWeighted_memLp (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) (u : Base → ℝ) (hu : Continuous u) :
    MemLp u 2 (sphereWeightedMeasure rho) := by
  let := sphereWeightedMeasure_finite rho hr hp
  exact hu.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace u)

def sphereWeightedToLp (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) (u : Base → ℝ) (hu : Continuous u) :
    Lp ℝ 2 (sphereWeightedMeasure rho) := (sphereWeighted_memLp rho hr hp u hu).toLp u

theorem sphereWeightedToLp_inner (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) (u v : Base → ℝ) (hu : Continuous u) (hv : Continuous v) :
    inner ℝ (sphereWeightedToLp rho hr hp u hu) (sphereWeightedToLp rho hr hp v hv) =
      sphereWeightedPairing rho u v := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, u x*v x ∂sphereWeightedMeasure rho := by
      apply integral_congr_ae
      filter_upwards [(sphereWeighted_memLp rho hr hp u hu).coeFn_toLp,
        (sphereWeighted_memLp rho hr hp v hv).coeFn_toLp] with x hx hy
      simp only [sphereWeightedToLp] at *
      rw [hx,hy]
      change v x*u x = u x*v x
      ring
    _ = _ := by
      rw [sphereWeightedMeasure_integral rho hr hp]
      simp only [sphereWeightedPairing,mul_assoc]

theorem sphereWeightedToLp_norm_sq (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) (u : Base → ℝ) (hu : Continuous u) :
    ‖sphereWeightedToLp rho hr hp u hu‖^2 = sphereWeightedPairing rho u u := by
  rw [← real_inner_self_eq_norm_sq,sphereWeightedToLp_inner]

end
end Yau.Target

end OAI
