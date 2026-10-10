import OAI.Geometry.RCD.Sobolev.LocalEnergyMeasure

namespace OAI

/-! # Localized energy integrals are exact masses of their image measure -/

open Set MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Y] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem localEnergyMeasure_map_apply (w : SobolevSpace μ hQ) (A : Set X)
    {c : ℝ} (hc : 0≤c) {v : X → Y} (hv : Measurable v)
    {B : Set Y} (hB : MeasurableSet B) :
    ((localEnergyMeasure μ hQ w A c).map v : Measure Y).real B=
      c*∫ x in v ⁻¹' B∩A, localGamma μ hQ w w x ∂μ := by
  change ((localEnergyMeasure μ hQ w A c : Measure X).map v B).toReal=_
  rw [Measure.map_apply hv hB]
  have he := localEnergyMeasure_apply μ hQ w A hc (hv hB)
  simpa only [Measure.real,Measure.restrict_restrict (hv hB)] using he

end RegularPointCoordinates

end

end OAI
