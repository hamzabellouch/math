import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEvolution
import OAI.MathematicalPhysics.Boltzmann.Branching.ThreeCollisionTimes

namespace OAI

/-! # Regrouping collision times and outgoing angles preserves their product law -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

private theorem pair_shuffle_preserving {A B D E : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace D] [MeasurableSpace E]
    (μ : Measure A) (ν : Measure B) (κ : Measure D) (τ : Measure E)
    [SFinite μ] [SFinite ν] [SFinite κ] [SFinite τ] :
    MeasurePreserving (fun q : (A × B) × (D × E) => ((q.1.1,q.2.1),(q.1.2,q.2.2)))
      ((μ.prod ν).prod (κ.prod τ)) ((μ.prod κ).prod (ν.prod τ)) := by
  have h₁ := measurePreserving_prodAssoc μ ν (κ.prod τ)
  have h₂ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc ν κ τ)
  have h₃ := (Measure.measurePreserving_swap (μ := ν) (ν := κ)).prod
    (MeasurePreserving.id τ)
  have h₄ := measurePreserving_prodAssoc κ ν τ
  have h₅ := (MeasurePreserving.id μ).prod (h₄.comp (h₃.comp h₂))
  have h₆ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ κ (ν.prod τ))
  exact h₆.comp (h₅.comp h₁)

abbrev ThreeAngles := Sphere × (Sphere × Sphere)
abbrev ThreeEvents := EventParameter × (EventParameter × EventParameter)

def splitThreeEvents (q : ThreeEvents) : ThreeWaits × ThreeAngles :=
  ((q.1.1,(q.2.1.1,q.2.2.1)),(q.1.2,(q.2.1.2,q.2.2.2)))

def joinThreeEvents (s : ThreeWaits) (a : ThreeAngles) : ThreeEvents :=
  ((s.1,a.1),((s.2.1,a.2.1),(s.2.2,a.2.2)))

theorem splitThreeEvents_preserving : MeasurePreserving splitThreeEvents
    (physicalEventMeasure.prod (physicalEventMeasure.prod physicalEventMeasure))
    ((volume : Measure ThreeWaits).prod
      (sphereProbability.prod (sphereProbability.prod sphereProbability))) := by
  have hi : MeasurePreserving
      (fun q : EventParameter × EventParameter => ((q.1.1,q.2.1),(q.1.2,q.2.2)))
      (physicalEventMeasure.prod physicalEventMeasure)
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
        (sphereProbability.prod sphereProbability)) :=
    pair_shuffle_preserving (volume : Measure ℝ) sphereProbability (volume : Measure ℝ) sphereProbability
  have h₁ := (MeasurePreserving.id physicalEventMeasure).prod hi
  have h₂ := pair_shuffle_preserving (volume : Measure ℝ) sphereProbability
    ((volume : Measure ℝ).prod (volume : Measure ℝ)) (sphereProbability.prod sphereProbability)
  convert h₂.comp h₁ using 1
  rfl

theorem three_events_lintegral {F : ThreeEvents → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalEventMeasure.prod (physicalEventMeasure.prod physicalEventMeasure)) =
      ∫⁻ s : ThreeWaits, ∫⁻ a : ThreeAngles, F (joinThreeEvents s a)
        ∂sphereProbability.prod (sphereProbability.prod sphereProbability) := by
  let : SFinite (sphereProbability.prod sphereProbability) := Measure.prod.instSFinite
  let : SFinite (sphereProbability.prod (sphereProbability.prod sphereProbability)) :=
    Measure.prod.instSFinite
  have hm : Measurable (fun q : ThreeWaits × ThreeAngles => F (joinThreeEvents q.1 q.2)) :=
    hF.comp (by unfold joinThreeEvents; fun_prop)
  rw [← lintegral_prod _ hm.aemeasurable]
  exact splitThreeEvents_preserving.lintegral_comp hm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
