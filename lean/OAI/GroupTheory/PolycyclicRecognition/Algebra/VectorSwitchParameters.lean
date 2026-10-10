import OAI.GroupTheory.PolycyclicRecognition.Algebra.SwitchParameterPullback
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-! # Finite vectors of independent pairs and the recursive switch law -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

def vectorSwitchParameters {A : Type*} :
    (k : ℕ) → (Fin k → A × A) → SwitchParameters A k
  | 0, _ => PUnit.unit
  | k + 1, p => ((p 0).1, (p 0).2, vectorSwitchParameters k (fun i => p i.succ))

theorem measurePreserving_vectorSwitchParameters {A : Type*} [MeasurableSpace A]
    (τ : Measure A) [IsProbabilityMeasure τ] (n k : ℕ) :
    MeasurePreserving (vectorSwitchParameters (A := A) k)
      (Measure.pi (fun _ : Fin k => τ.prod τ)) (switchParameterLaw (fun _ => τ) n k) := by
  induction k generalizing n with
  | zero =>
    refine ⟨measurable_const, ?_⟩
    simp [vectorSwitchParameters, switchParameterLaw]
  | succ k ih =>
    have hhead := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => τ.prod τ) 0
    have htail := (MeasurePreserving.id (τ.prod τ)).prod (ih (n + 1))
    have hassoc := measurePreserving_prodAssoc τ τ (switchParameterLaw (fun _ => τ) (n + 1) k)
    change MeasurePreserving _ _ (τ.prod (τ.prod (switchParameterLaw (fun _ => τ) (n + 1) k)))
    convert hassoc.comp (htail.comp hhead) using 1
    funext p
    simp [vectorSwitchParameters, Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply]
    rfl

end PolycyclicRecognition

end

end OAI
