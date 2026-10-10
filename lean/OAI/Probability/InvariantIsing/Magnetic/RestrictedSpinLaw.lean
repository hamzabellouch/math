import OAI.Probability.InvariantIsing.Core.ConditionalRelativeEntropy
import OAI.Probability.InvariantIsing.Fields.CanonicalSpinWeights
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldTerminal

namespace OAI

/-! The constrained terminal spin distribution is the physical Gibbs
law conditioned on the allowed spins. Its entropy cost is exactly the
loss in log partition functions, retaining the original cube mass. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma spinGibbs_mass_finset {N : ℕ} (H : Spin N → ℝ) (S : Finset (Spin N)) :
    (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real S =
      (∑ σ ∈ S, Real.exp (H σ)) / ∑ σ, Real.exp (H σ) := by
  classical
  rw [← integral_indicator_one (μ := gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H)
    S.measurableSet, integral_uniformSpinGibbs_canonical]
  simp only [Set.indicator, Pi.one_apply, Finset.mem_coe,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  simp only [finiteCanonicalWeights, Finset.sum_div]

lemma spinGibbs_mass_pos {N : ℕ} (H : Spin N → ℝ) (S : Finset (Spin N)) (hS : S.Nonempty) :
    0 < (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real S := by
  rw [spinGibbs_mass_finset]
  exact div_pos (Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS) (sum_exp_pos H)

def restrictedSpinLaw {N : ℕ} (S : Finset (Spin N)) (H : Spin N → ℝ) : Measure (Spin N) :=
  cond (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H) S

lemma restrictedSpinLaw_probability {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) : IsProbabilityMeasure (restrictedSpinLaw S H) := by
  apply cond_isProbabilityMeasure
  exact (measureReal_ne_zero_iff).mp (spinGibbs_mass_pos H S hS).ne'

theorem restrictedSpinLaw_entropy {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) :
    klDiv (restrictedSpinLaw S H) (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H) ≠ ⊤ ∧
      (klDiv (restrictedSpinLaw S H)
        (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H)).toReal =
      logPartition H - restrictedSpinLog S H := by
  have he := conditioned_measure_entropy
    (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H) S S.measurableSet
    ((measureReal_ne_zero_iff).mp (spinGibbs_mass_pos H S hS).ne')
  refine ⟨he.1, he.2.trans ?_⟩
  rw [spinGibbs_mass_finset, Real.log_div
    (Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS).ne' (sum_exp_pos H).ne']
  rw [logPartition_eq, log_card_spin, restrictedSpinLog]
  ring

end InvariantIsing

end

end OAI
