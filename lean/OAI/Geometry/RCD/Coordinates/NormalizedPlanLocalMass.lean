import OAI.Geometry.RCD.Sobolev.LocalEnergyMap
import OAI.Geometry.RCD.Coordinates.NormalizedPlanMeanEnergy

namespace OAI

/-! # Mean-energy control by the exact localized image-measure mass -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [MeasurableSpace Y]
attribute [local instance] pathBorel pathBorelSpace

theorem SobolevSpace.normalized_plan_local_mass (μ : Measure X) [μ.Regular]
    (hQ : QuadraticCheegerEnergy μ) (w : SobolevSpace μ hQ)
    (P : ProbabilityMeasure C(Time,X))
    (hgeo : ∀ᵐ γ ∂(P : Measure C(Time,X)), IsGeodesic γ)
    {r a : ℝ} (hr : 0<r) (ha : 0≤a) {V : ℝ≥0∞} (hV : 0<V.toReal)
    (hcomp : ∀ t : Time, (P : Measure C(Time,X)).map (fun γ => γ t)≤
      (ENNReal.ofReal a*V⁻¹) • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 (P : Measure C(Time,X)))
    (A : Set X) {v : X → Y} (hv : Measurable v) {B : Set Y} (hB : MeasurableSet B)
    (hstay : ∀ t : Time, ∀ᵐ x ∂(P : Measure C(Time,X)).map (fun γ => γ t),
      x∈v ⁻¹' B∩A) :
    ((∫ γ : C(Time,X), SobolevSpace.toLp μ hQ w (γ 1) ∂(P : Measure C(Time,X)))-
      (∫ γ : C(Time,X), SobolevSpace.toLp μ hQ w (γ 0) ∂(P : Measure C(Time,X))))^2≤
      (∫ γ : C(Time,X), (dist (γ 0) (γ 1)/r)^2 ∂(P : Measure C(Time,X)))*a*
        ((localEnergyMeasure μ hQ w A (r^2/V.toReal)).map v : Measure Y).real B := by
  rw [localEnergyMeasure_map_apply μ hQ w A (div_nonneg (sq_nonneg _) hV.le) hv hB]
  exact w.normalized_plan_mean_energy μ hQ P hgeo hr ha hV hcomp hD hstay

end RegularPointCoordinates

end

end OAI
