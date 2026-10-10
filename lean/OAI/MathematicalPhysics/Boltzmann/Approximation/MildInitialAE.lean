import OAI.MathematicalPhysics.Boltzmann.Jets.ColdMildRepresentative

namespace OAI

/-! # Initial traces of the a.e. characteristic equations -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

namespace PositiveIntegral

theorem value_zero {T : ℝ} (_hT : 0 ≤ T) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) (g : ℝ × JetPrototype.Phase → ℝ) (p : JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g (0,p) = f₀ p := by
  simp [value,time,JetBarrier.flight]

end PositiveIntegral

namespace WeightedLocal

theorem MildAE.initial_ae {q b L T : ℝ} (hT : 0 ≤ T)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    (he : MildAE q b L T F₀ F) :
    (fun p => F (0,p)) =ᵐ[FlightMeasure.phaseVolume] F₀ := by
  simpa only [PositiveIntegral.value_zero hT] using he 0 ⟨le_rfl,hT⟩

theorem ColdMildAE.initial_ae {q b L T : ℝ} (hT : 0 ≤ T)
    {F c : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (he : ColdMildAE q b L T F c₀ c) :
    (fun p => c (0,p)) =ᵐ[FlightMeasure.phaseVolume] c₀ := by
  simpa only [PositiveIntegral.value_zero hT] using he 0 ⟨le_rfl,hT⟩

end WeightedLocal
end BoltzmannNonuniqueness

end

end OAI
