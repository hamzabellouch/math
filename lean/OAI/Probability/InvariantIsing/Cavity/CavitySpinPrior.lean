import OAI.Probability.InvariantIsing.Cavity.CavitySpinIsometry
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorLabeled

namespace OAI

/-! Exact prior symmetries for the signed-site action. The cascade
leaf coordinate stays fixed and retains its original random prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma uniformSpinPrior_equiv {N : ℕ} (e : Equiv.Perm (Spin N)) :
    MeasurePreserving e (uniformSpinPrior N : Measure (Spin N))
      (uniformSpinPrior N : Measure (Spin N)) := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_singleton
  intro σ
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton σ)]
  have hp : e ⁻¹' {σ} = {e.symm σ} := by
    ext τ
    exact e.eq_symm_apply.symm
  rw [hp]
  change (PMF.uniformOfFintype (Spin N)).toMeasure {e.symm σ} =
    (PMF.uniformOfFintype (Spin N)).toMeasure {σ}
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]

lemma labeledSpinReference_equiv {N depth : ℕ} (e : Equiv.Perm (Spin N))
    (T : LabeledTree depth) :
    MeasurePreserving (fun x : Spin N × LabeledLeaf depth => (e x.1, x.2))
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T) := by
  exact (uniformSpinPrior_equiv e).prod (MeasurePreserving.id _)

end InvariantIsing

end

end OAI
