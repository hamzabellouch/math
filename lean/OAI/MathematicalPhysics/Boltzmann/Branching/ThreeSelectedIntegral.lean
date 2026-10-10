import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedOriginDeletion
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionParameterShuffle

namespace OAI

/-! # Three selected collisions as one time and angle integral -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def threeSelectedIntegrand (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m₀ m₁ m₂ : HistoryMark) (p : PhysicalFlightState) (F : PhysicalFlightState → ℝ≥0∞)
    (q : ThreeEvents) : ℝ≥0∞ :=
  let a : CollisionWord 3 := (q.1,(q.2.1,(q.2.2,PUnit.unit)))
  selectedWordDensity b endTime C [m₀,m₁,m₂] p a *
    F (selectedWordState b endTime [m₀,m₁,m₂] p a)

theorem threeSelectedIntegrand_measurable (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m₀ m₁ m₂ : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    Measurable (threeSelectedIntegrand b endTime C m₀ m₁ m₂ p F) := by
  have hm : Measurable (fun q : ThreeEvents =>
      (p,((q.1,(q.2.1,(q.2.2,PUnit.unit))) : CollisionWord 3))) := by fun_prop
  exact ((selectedWordDensity_measurable b endTime C [m₀,m₁,m₂]).comp hm).mul
    (hF.comp ((selectedWordState_measurable b endTime [m₀,m₁,m₂]).comp hm))

theorem threeSelected_integral (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m₀ m₁ m₂ : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, threeSelectedIntegrand b endTime C m₀ m₁ m₂ p F q
      ∂physicalEventMeasure.prod (physicalEventMeasure.prod physicalEventMeasure)) =
      ∫⁻ q, F q ∂physicalMarkedWord b endTime C [m₀,m₁,m₂] p := by
  have hd := (MeasurePreserving.id physicalEventMeasure).prod
    ((MeasurePreserving.id physicalEventMeasure).prod
      (measurePreserving_fst (μ := physicalEventMeasure) (ν := Measure.dirac PUnit.unit)))
  rw [← hd.lintegral_comp (threeSelectedIntegrand_measurable b endTime C m₀ m₁ m₂ p hF)]
  rw [← selectedWord_integral b endTime C [m₀,m₁,m₂] p hF]
  apply lintegral_congr
  intro a
  rcases a with ⟨a₀,a₁,a₂,u⟩
  cases u
  rfl

theorem threeSelected_time_angles (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m₀ m₁ m₂ : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalMarkedWord b endTime C [m₀,m₁,m₂] p) =
      ∫⁻ s : ThreeWaits, ∫⁻ a : ThreeAngles,
        threeSelectedIntegrand b endTime C m₀ m₁ m₂ p F (joinThreeEvents s a)
          ∂sphereProbability.prod (sphereProbability.prod sphereProbability) := by
  rw [← threeSelected_integral b endTime C m₀ m₁ m₂ p hF]
  exact three_events_lintegral (threeSelectedIntegrand_measurable b endTime C m₀ m₁ m₂ p hF)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
