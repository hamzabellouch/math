import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinLaw
import OAI.Probability.InvariantIsing.Fields.FieldVectorSampling

namespace OAI

/-! The actual constrained terminal spin kernel, including measurability
and its exact conditional entropy cost. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron Set

namespace InvariantIsing

def restrictedSpinKernel {N : ℕ} (S : Finset (Spin N)) : Kernel (Fin N → ℝ) (Spin N) := by
  refine ⟨fun z => restrictedSpinLaw S (fieldEnergy z), ?_⟩
  apply Measure.measurable_of_measurable_coe
  intro T hT
  change Measurable (fun z => cond (fieldVectorSpinKernel N z) S T)
  simp only [cond_apply S.measurableSet]
  exact ((fieldVectorSpinKernel N).measurable_coe S.measurableSet).inv.mul
    ((fieldVectorSpinKernel N).measurable_coe (S.measurableSet.inter hT))

lemma restrictedSpinKernel_markov {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    IsMarkovKernel (restrictedSpinKernel S) :=
  ⟨fun z => restrictedSpinLaw_probability S hS (fieldEnergy z)⟩

lemma restrictedSpinKernel_univ (N : ℕ) :
    restrictedSpinKernel (Finset.univ : Finset (Spin N)) = fieldVectorSpinKernel N := by
  ext z : 1
  change cond (fieldVectorSpinKernel N z) (Finset.univ : Finset (Spin N)) = _
  simpa only [Finset.coe_univ] using (cond_univ (μ := fieldVectorSpinKernel N z))

theorem restrictedSpinKernel_entropy {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (z : Fin N → ℝ) :
    klDiv (restrictedSpinKernel S z) (fieldVectorSpinKernel N z) ≠ ⊤ ∧
      (klDiv (restrictedSpinKernel S z) (fieldVectorSpinKernel N z)).toReal =
        restrictedFieldTerminal Finset.univ z - restrictedFieldTerminal S z := by
  have he := restrictedSpinLaw_entropy S hS (fieldEnergy z)
  rw [← restrictedSpinLog_univ] at he
  exact he

end InvariantIsing

end

end OAI
