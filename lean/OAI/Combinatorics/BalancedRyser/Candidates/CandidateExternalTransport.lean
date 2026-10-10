import OAI.Combinatorics.BalancedRyser.Candidates.CandidateValidityAssembly
import OAI.Combinatorics.BalancedRyser.Candidates.ExternalWitnessModel
import OAI.Combinatorics.BalancedRyser.Probability.ProbabilityPerturbation

namespace OAI

namespace Balanced.CandidateValidityAssembly

noncomputable section
open scoped Classical BigOperators
open TupleAlignment CandidateValidityWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem externalFailures_witness_cover (M : MergedPairs F) (g : Direction F)
    (a : RootPrescription g) (ha : a ∈ externalFailures M g) :
    ∃ w ∈ ExternalAssembly.witnesses g M, w.1.1 = a.tuple := by
  obtain ⟨hs, hext⟩ := Finset.mem_filter.mp ha
  have hsuccess := successfulOn_of_mem hs
  have hline : ExternalAssembly.targetLine g M a.tuple = (a.choice M).line := rfl
  obtain ⟨ij, de, hw⟩ := (ExternalAssembly.exists_witness_iff g M a.tuple).mpr
    (by simpa only [hline] using And.intro hsuccess hext)
  exact ⟨((a.tuple, ij), de), hw, rfl⟩

theorem externalFailures_card_le_witnesses (M : MergedPairs F) (g : Direction F) :
    (externalFailures M g).card ≤ (ExternalAssembly.witnesses g M).card :=
  card_le_witnesses (externalFailures M g) (ExternalAssembly.witnesses g M)
    (fun w => w.1.1) (externalFailures_witness_cover M g)

theorem externalFailures_some_tail_le (t : ℝ) :
    offsetEventProbability {M : MergedPairs F | ∃ g,
      t ≤ ((externalFailures M g).card : ℝ)} ≤
    offsetEventProbability {M : MergedPairs F | ∃ g,
      t ≤ ((ExternalAssembly.witnesses g M).card : ℝ)} := by
  apply pmf_outerReal_mono (offsetLaw F)
  rintro M ⟨g, hg⟩
  exact ⟨g, hg.trans (Nat.cast_le.mpr (externalFailures_card_le_witnesses M g))⟩

theorem externalFailures_moment_le_witnesses (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (s : ℕ) :
    (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
      ((externalFailures M g).card : ℝ)^s) ≤
    ∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
      ((ExternalAssembly.witnesses g M).card : ℝ)^s := by
  apply Finset.sum_le_sum
  intro M _
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg _)
      (Nat.cast_le.mpr (externalFailures_card_le_witnesses M g)) s)
    ENNReal.toReal_nonneg

end
end Balanced.CandidateValidityAssembly

end OAI
