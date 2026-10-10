import OAI.GroupTheory.PolycyclicRecognition.Algebra.VectorSwitchParameters
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ParameterSplit

namespace OAI

/-! # The recursive independent sampling law on the flat parameter cube -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

/-- The first block holds first samples and the second block holds second samples. -/
def flatSamplePairs (m : ℕ) (t : Fin (m + m) → ℝ) : Fin m → ℝ × ℝ :=
  fun j => (t (Fin.castAdd m j), t (Fin.natAdd m j))

def flatSwitchSamples (m : ℕ) (t : Fin (m + m) → ℝ) : SwitchParameters ℝ m :=
  vectorSwitchParameters m (flatSamplePairs m t)

theorem measurePreserving_finAppend_law (τ : Measure ℝ) [SigmaFinite τ] (n k : ℕ) :
    MeasurePreserving (fun p : (Fin n → ℝ) × (Fin k → ℝ) => Fin.append p.1 p.2)
      ((Measure.pi (fun _ => τ)).prod (Measure.pi (fun _ => τ)))
      (Measure.pi (fun _ => τ)) := by
  have h₁ := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin k => τ)
  have h₂ := measurePreserving_piCongrLeft (fun _ : Fin (n + k) => τ) finSumFinEquiv
  convert h₂.comp h₁ using 1
  ext p i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  simp only [Function.comp_apply]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases j with
  | inl j =>
    change Fin.append p.1 p.2 (Fin.castAdd k j) = p.1 j
    simp
  | inr j =>
    change Fin.append p.1 p.2 (Fin.natAdd n j) = p.2 j
    simp

theorem measurePreserving_flatSamplePairs (τ : Measure ℝ) [SigmaFinite τ] (m : ℕ) :
    MeasurePreserving (flatSamplePairs m)
      (Measure.pi (fun _ => τ)) (Measure.pi (fun _ : Fin m => τ.prod τ)) := by
  let e := (Fin.appendIsometry (α := ℝ) m m).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e
      ((Measure.pi (fun _ => τ)).prod (Measure.pi (fun _ => τ)))
      (Measure.pi (fun _ => τ)) := measurePreserving_finAppend_law τ m m
  have hp := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin m)
    (fun _ => τ) (fun _ => τ)).symm (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin m))
  convert hp.comp (he.symm e) using 1
  ext t j <;> rfl

theorem measurePreserving_flatSwitchSamples (τ : Measure ℝ) [IsProbabilityMeasure τ]
    (n m : ℕ) :
    MeasurePreserving (flatSwitchSamples m)
      (Measure.pi (fun _ => τ)) (switchParameterLaw (fun _ => τ) n m) :=
  (measurePreserving_vectorSwitchParameters τ n m).comp (measurePreserving_flatSamplePairs τ m)

end PolycyclicRecognition

end

end OAI
