import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingDriftSupport
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneImpulseScalar

namespace OAI

/-! The prescribed full recorder array satisfies the precise compact
coefficient hypotheses of the published whole-plane scalar input. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Set MeasureTheory

theorem expandingDrift_compact_coefficients (M : Alternating.Machine)
    (hM : M.WellFormed) (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) (p : Plane) :
    CompactPlaneCoefficients (expandingDrift M hM blank m ν D K) (unitImpulse p) := by
  intro T _
  obtain ⟨L, hL, hz⟩ := expandingDrift_compact_on_finite_intervals M hM blank m hν hD hK T
  refine ⟨L ∪ tsupport (spatialImpulse p), hL.union (spatialImpulse_compactSupport p).isCompact, ?_⟩
  intro t ht x hx
  have hxl : x ∉ L := fun h => hx (Or.inl h)
  have hxp : x ∉ tsupport (spatialImpulse p) := fun h => hx (Or.inr h)
  refine ⟨hz t ht x hxl, ?_⟩
  change smoothPulse 0 1 t * spatialImpulse p x = 0
  rw [image_eq_zero_of_notMem_tsupport hxp, mul_zero]

theorem expanding_scalar_exists (hE : PlaneScalarExistence)
    (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) (p : Plane) :
    ∃ w : ℝ → Plane → ℝ,
      GlobalPlaneScalarSolution ν (expandingDrift M hM blank m ν D K) (unitImpulse p) w ∧
      (∀ t, 0 ≤ t → ∀ x, 0 ≤ w t x) ∧
      (∀ t, 0 ≤ t → Integrable (w t)) ∧
      (∀ t, 0 ≤ t → (∫ x, w t x) = smoothRamp 0 1 t) :=
  unitImpulse_scalar_exists hE ν hν _ p
    (expandingDrift_smooth M hM blank m hν hD hK)
    (expandingDrift_compact_coefficients M hM blank m hν hD hK p)
    (expandingDrift_divergence M hM blank m hν hD hK)

end ForcedComputation.ExpandingDetector

end

end OAI
