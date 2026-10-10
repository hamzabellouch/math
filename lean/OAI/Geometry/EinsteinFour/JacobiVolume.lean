import OAI.Geometry.EinsteinFour.AveragedRadial
import OAI.Geometry.EinsteinFour.AveragedVolume

namespace OAI

/-! The upper volume estimate from the Jacobi ODE, curvature-field identities,
energy bounds, and the polar volume formula. -/

namespace PositiveEinsteinFour.Jacobi

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

local instance : NormedAddCommGroup NormalMatrix := Matrix.frobeniusNormedAddCommGroup
local instance : NormedSpace ℝ NormalMatrix := Matrix.frobeniusNormedSpace

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

local instance : NormedAddCommGroup C(Ω, NormalMatrix) :=
  ContinuousMap.instNormedAddCommGroup
local instance : NormedSpace ℝ C(Ω, NormalMatrix) := ContinuousMap.normedSpace

/-- Equation (7) from the actual Jacobi ODE and the two geodesic field
identities. -/
theorem volume_ratio_upper_of_jacobi
    (d : (u : ℝ) → Ω → RegularJacobi (Real.pi * u))
    {F G : ℝ → C(Ω, NormalMatrix)} {V s : ℝ}
    (hs : 0 ≤ s)
    (hderiv : ∀ r, HasDerivAt F (G r) r)
    (hstationary : ∀ r, (∫ x, ‖F r x‖ ^ 2 ∂μ) = (3 / 2) * s)
    (henergy : ∀ r, (∫ x, ‖G r x‖ ^ 2 ∂μ) ≤ (3 / 2) * ((3 / 2) * s))
    (hcurvature : ∀ u x r, (d u x).R r = 1 + F r x)
    (hpos : ∀ u x r, ((d u x).R r).PosSemidef)
    (htrace : ∀ u x r, ((d u x).R r).trace = 3)
    (hLip : ∀ u, 0 < u → u < 1 → ∀ x, ∃ L : ℝ, 0 ≤ L ∧ ∀ a b,
      ‖Averages.sineWeight a • radialCurvature (d u x).R (Real.pi * u) a -
        Averages.sineWeight b • radialCurvature (d u x).R (Real.pi * u) b‖ ≤ L * |a - b|)
    (hD : ∀ u, 0 < u → u < 1 → Integrable (fun x => (d u x).truncatedDensity) μ)
    (hD0 : IntervalIntegrable (fun u => ∫ x, (d u x).truncatedDensity ∂μ)
      volume 0 (5 / 8))
    (hD1 : IntervalIntegrable (fun u => ∫ x, (d u x).truncatedDensity ∂μ)
      volume (5 / 8) 1)
    (hpolar : V ≤ (3 * Real.pi / 4) *
      ((∫ u in (0 : ℝ)..(5 / 8), ∫ x, (d u x).truncatedDensity ∂μ) +
        ∫ u in (5 / 8 : ℝ)..1, ∫ x, (d u x).truncatedDensity ∂μ)) :
    V ≤ 1 - (3 / 40) * s := by
  apply volume_ratio_upper_of_averaged_radial hs hD0 hD1 hpolar
  intro u hu hu1
  exact averaged_truncatedDensity_le (d u) (mul_pos Real.pi_pos hu)
    (by nlinarith [Real.pi_pos]) (by positivity) hderiv hstationary henergy
    (hcurvature u) (hpos u) (htrace u) (hLip u hu hu1) (hD u hu hu1)

end

end PositiveEinsteinFour.Jacobi

end OAI
