import OAI.Geometry.RCD.Harmonic.RadialCompactnessSequence
import OAI.Geometry.RCD.Sobolev.RescaledHarmonicEnergy

namespace OAI

/-! # Replacing the harmonic member of a fixed geometric sequence -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
/-- The radial and coordinate convergence data remain unchanged when
an arbitrary normalized harmonic sequence replaces the harmonic member.
The local energy bound follows from Jiang's published interior estimate. -/
def RadialCompactnessSequence.with_harmonic {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} {S : ℝ} (q : RadialCompactnessSequence hX S)
    (hgradient : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n) (hS : 0 < S)
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball (q.center i) (S * q.radius i)) (w i))
    (hwnorm : ∀ i, ‖normalizeLocalL2 (hausdorff n X) (ball (q.center i) (S * q.radius i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (q.center i) (S * q.radius i)) (w i))‖ ≤ 1) :
    RadialCompactnessSequence hX S where
  center := q.center
  radius := q.radius
  error := q.error
  coordinates := q.coordinates
  coordinateValues := q.coordinateValues
  harmonicFunction := w
  radialFunction := q.radialFunction
  radius_pos := q.radius_pos
  curvature := q.curvature
  error_pos := q.error_pos
  error_zero := q.error_zero
  measured := q.measured
  representative := q.representative
  harmonic := hw
  outer_norm := hwnorm
  interior_energy := by
    intro ρ hρ hρS
    obtain ⟨C, hC, hb⟩ := hgradient.rescaled_interior_energy hn hS hρ hρS
    exact ⟨C, hC, fun i => hb (q.center i) (q.radius i) (q.radius_pos i)
      (q.curvature i) (w i) (hw i) (hwnorm i)⟩
  radial_bounds := q.radial_bounds
  quadratic_limit := q.quadratic_limit

end RegularPointCoordinates

end

end OAI
