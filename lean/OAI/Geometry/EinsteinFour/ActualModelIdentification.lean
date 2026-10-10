import OAI.Geometry.EinsteinFour.GeodesicGeometry12
import OAI.Geometry.EinsteinFour.GeodesicGeometry14

namespace OAI

/-! Actual half-conformally-flat model identification. All analytic,
index, injectivity, and metric-model inputs are supplied by proved geometry. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actual_halfFlat_positive_harmonic_dimension_one (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hplus : ∃ x, plusWeyl g x (o.frame x) ≠ 0) :
    Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1 :=
  halfFlat_positive_harmonic_dimension_one_of_injective_ball hRic hpositive hminus hplus
    (actual_frameExponential_injOn_sqrt_three g o hRic hpositive)

theorem actual_halfFlat_models (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0) :
    ∃ a : ℝ, 0 < a ∧ (ScaledIsometricTo g a roundDistance ∨
      ScaledIsometricTo g a fubiniStudyDistance) := by
  by_cases hp : ∀ x, plusWeyl g x (o.frame x) = 0
  · exact ⟨1,by norm_num,Or.inl (actual_round_model hRic hpositive hp hminus)⟩
  · have hn : ∃ x, plusWeyl g x (o.frame x) ≠ 0 := not_forall.mp hp
    exact ⟨1/2,by norm_num,Or.inr (actual_complex_projective_model hRic hminus
      (actual_halfFlat_positive_harmonic_dimension_one hRic hpositive hminus hn))⟩

variable [ConnectedSpace M]

omit [CompactSpace M] [SecondCountableTopology M] [ConnectedSpace M] [PreconnectedSpace M] in
theorem actual_derdzinski_hitchin (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) : DerdzinskiHitchinInput g o := by
  intro _ _ _ _ _ hpositive hblock
  rcases hblock with hplus | hminus
  · have hminus : ∀ x, minusWeyl g x (o.reversed.frame x) = 0 := by
      intro x
      apply (minusNorm_eq_zero_iff o.reversed x).mp
      rw [minusNorm_reversed]
      exact (plusNorm_eq_zero_iff o x).mpr (hplus x)
    exact actual_halfFlat_models hRic hpositive hminus
  · exact actual_halfFlat_models hRic hpositive hminus

end
end PositiveEinsteinFour.Geometry

namespace PositiveEinsteinFour
open EinsteinFour _root_.OAI.PositiveEinsteinFour.Geometry
open scoped Manifold ContDiff
noncomputable section
universe u

/-- Every connected closed oriented positively curved Einstein four-manifold is,
up to positive scaling and isometry, the round S4 or Fubini–Study CP2. -/
theorem orientedClassification (X : ClosedOrientedMetricFour.{u})
    (hEinstein : IsEinstein X.metric) (hpositive : HasPositiveSectionalCurvature X.metric) :
    ∃ a : ℝ, 0 < a ∧ (ScaledIsometricTo X.metric a roundDistance ∨
      ScaledIsometricTo X.metric a fubiniStudyDistance) := by
  let : MeasurableSpace X.manifold := borel X.manifold
  let : BorelSpace X.manifold := ⟨rfl⟩
  exact models_of_actual_model_inputs X.metric X.orientation
    actual_derdzinski_hitchin hEinstein hpositive

variable (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M] [ConnectedSpace M]

/-- Every closed connected positively curved Einstein four-manifold is,
up to positive scaling and isometry, standard S4, CP2, or RP4. -/
theorem classificationOn : ClassificationOn M := by
  apply classificationOn_of_model_inputs
  refine ⟨?_⟩
  intro X
  let : MeasurableSpace X.manifold := borel X.manifold
  let : BorelSpace X.manifold := ⟨rfl⟩
  intro g o hRic
  exact actual_derdzinski_hitchin g o hRic

end
end PositiveEinsteinFour

end OAI
