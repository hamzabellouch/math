import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedGeometricBlock

namespace OAI

/-! # Separate collision and free-waiting laws preserve the reachable cone -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedDensityScaledCollision_ae_fixed (C : ℝ≥0) (b : BeamCoefficients)
    (T : ℝ) (ρ : ℝ≥0) (p : PhysicalFlightState) :
    ∀ᵐ q ∂dampedDensityScaledCollision C b T ρ p, q.1 = p.1 ∧ q.2.1 = p.2.1 := by
  let A : Set PhysicalFlightState := {q | ¬(q.1 = p.1 ∧ q.2.1 = p.2.1)}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hF : Measurable (A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) :=
    measurable_const.indicator hA
  rw [ae_iff]
  change dampedDensityScaledCollision C b T ρ p A = 0
  rw [← lintegral_indicator_one hA,dampedDensityScaledCollision_lintegral C b T ρ p hF,
    dampedMediumStateCollision_lintegral C b T p hF]
  have hz (v : V) : A.indicator (1 : PhysicalFlightState → ℝ≥0∞) (p.1,(p.2.1,v)) = 0 := by
    apply indicator_of_notMem
    simp [A]
  simp only [hz,lintegral_zero,mul_zero]

theorem boundedCollision_ae_cone (C : ℝ≥0) (b : BeamCoefficients) (T : ℝ) (ρ : ℝ≥0)
    {p q : PhysicalFlightState} (hq : boundedFlightCone p q) :
    ∀ᵐ r ∂(dampedDensityScaledCollision C b T ρ q).restrict mediumVelocityBox,
      boundedFlightCone p r := by
  filter_upwards [ae_restrict_of_ae (dampedDensityScaledCollision_ae_fixed C b T ρ q),
    ae_restrict_mem mediumVelocityBox_measurable] with r hr hv
  exact ⟨hr.1 ▸ hq.1,hr.1 ▸ hq.2.1,hv,by rw [hr.1,hr.2]; exact hq.2.2.2⟩

theorem physicalWaitingKernel_ae_cone (C : ℝ≥0) (p : PhysicalFlightState) (hp : ‖p.2.2‖ ≤ 6) :
    ∀ᵐ q ∂physicalWaitingKernel C p, boundedFlightCone p q := by
  let A : Set PhysicalFlightState := {q | ¬boundedFlightCone p q}
  have hA : MeasurableSet A := (boundedFlightCone_measurable p).compl
  have hF : Measurable (A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) :=
    measurable_const.indicator hA
  rw [ae_iff]
  change physicalWaitingKernel C p A = 0
  rw [← lintegral_indicator_one hA,physicalWaitingKernel_lintegral C p hF]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hz : A.indicator (1 : PhysicalFlightState → ℝ≥0∞) (physicalAdvance p s) = 0 := by
    apply indicator_of_notMem
    exact fun h => h (boundedFlightCone_step hs hp hp)
  rw [hz,mul_zero]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
