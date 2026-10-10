import OAI.Probability.DilutedSpin.Core

namespace OAI

section
section
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory

variable {X : Type} [MeasurableSpace X]

noncomputable def rootArrayEquiv : (n : ℕ) → RootPath X n ≃ᵐ (Fin n → X)
  | 0 => MeasurableEquiv.ofUniqueOfUnique _ _
  | n+1 => ((MeasurableEquiv.refl X).prodCongr (rootArrayEquiv n)).trans
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) 0).symm

lemma rootArrayEquiv_apply (n : ℕ) (x : RootPath X n) : rootArrayEquiv (X := X) n x = rootArray n x := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    change Fin.insertNth 0 x.1 (rootArrayEquiv (X := X) n x.2) =
      Fin.cons (α := fun _ : Fin (n+1) => X) x.1 (rootArray n x.2)
    rw [Fin.insertNth_zero', ih]


/-- Exact law identification for arbitrary measurable disorder alphabets,
including the continuous physical interaction tables and external fields. -/
theorem measurePreserving_rootArray (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (rootArrayEquiv (X := X) n) (rootLaw n (fun _ => μ))
      (Measure.pi (fun _ : Fin n => μ)) := by
  induction n with
  | zero =>
    refine ⟨(rootArrayEquiv 0).measurable, ?_⟩
    rw [rootLaw,Measure.map_dirac' (rootArrayEquiv 0).measurable,Measure.pi_of_empty]
    congr 1
  | succ n ih =>
    exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm.comp
      ((MeasurePreserving.id μ).prod ih)

theorem integral_rootArray_eq_pi (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (f : (Fin n → X) → ℝ) :
    (∫ x, f (rootArray n x) ∂rootLaw n (fun _ => μ)) =
      ∫ x, f x ∂Measure.pi (fun _ : Fin n => μ) := by
  simpa only [rootArrayEquiv_apply] using (measurePreserving_rootArray μ n).integral_comp' f

end DilutedSpinGlass
end

end

end OAI
