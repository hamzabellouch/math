import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinPrior
import OAI.Probability.InvariantIsing.Cavity.CavitySpinPrior

namespace OAI

/-! A spin permutation preserving a constraint preserves its normalized
prior and its product with the actual cascade leaf law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem restrictedSpinPrior_equiv {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (e : Spin N ≃ Spin N) (hinv : ∀ σ, e σ ∈ S ↔ σ ∈ S) :
    MeasurePreserving e (restrictedSpinPrior S hS : Measure (Spin N))
      (restrictedSpinPrior S hS : Measure (Spin N)) := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_singleton
  intro σ
  have hp : e ⁻¹' {σ} = {e.symm σ} := by
    ext τ
    exact e.eq_symm_apply.symm
  have hi : e.symm σ ∈ S ↔ σ ∈ S := by
    simpa only [e.apply_symm_apply] using (hinv (e.symm σ)).symm
  have he : ((restrictedSpinPrior S hS : Measure (Spin N)).map e).real {σ} =
      (restrictedSpinPrior S hS : Measure (Spin N)).real {σ} := by
    rw [measureReal_def, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton σ), hp]
    change (restrictedSpinPrior S hS : Measure (Spin N)).real {e.symm σ} = _
    simp only [restrictedSpinPrior_singleton, hi]
  have hh := congrArg ENNReal.ofReal he
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh

theorem restricted_labeled_spin_reference_equiv {N depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (T : LabeledTree depth)
    (e : Spin N ≃ Spin N) (hinv : ∀ σ, e σ ∈ S ↔ σ ∈ S) :
    MeasurePreserving (fun x : Spin N × LabeledLeaf depth => (e x.1, x.2))
      (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
      (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T) :=
  (restrictedSpinPrior_equiv S hS e hinv).prod (MeasurePreserving.id (labeledLeafLaw depth T))

end InvariantIsing

end

end OAI
