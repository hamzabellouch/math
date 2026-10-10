import OAI.Combinatorics.BalancedRyser.Candidates.CandidateValidityAssembly
import OAI.Combinatorics.BalancedRyser.Candidates.OppositeTail
import OAI.Combinatorics.BalancedRyser.Probability.ProbabilityPerturbation

namespace OAI

namespace Balanced.CandidateValidityAssembly

noncomputable section
open scoped Classical Topology
open TupleAlignment CandidateExposure CandidateValidityWitness Filter

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem oppositeFailures_witness_cover (M : MergedPairs F) (g : Direction F)
    (a : RootPrescription g) (ha : a ∈ oppositeFailures M g) :
    ∃ w ∈ OppositeAssembly.witnesses g M, w.1.1 = a.tuple := by
  obtain ⟨hs, i, d, hd, hdT, hp⟩ := Finset.mem_filter.mp ha
  refine ⟨((a.tuple, i), d), ?_, rfl⟩
  apply (OppositeAssembly.mem_witnesses g M a.tuple i d).mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.injective,
    fun j => (a.1 j).2⟩, ?_, hd, hdT, hp⟩
  exact (Finset.mem_filter.mp hs).2

theorem oppositeFailures_card_le_witnesses (M : MergedPairs F) (g : Direction F) :
    (oppositeFailures M g).card ≤ (OppositeAssembly.witnesses g M).card :=
  card_le_witnesses (oppositeFailures M g) (OppositeAssembly.witnesses g M)
    (fun w => w.1.1) (oppositeFailures_witness_cover M g)

theorem oppositeFailures_some_tail_le (t : ℝ) :
    offsetEventProbability {M : MergedPairs F | ∃ g,
      t ≤ ((oppositeFailures M g).card : ℝ)} ≤
    offsetEventProbability {M : MergedPairs F | ∃ g,
      t ≤ ((OppositeAssembly.witnesses g M).card : ℝ)} := by
  apply pmf_outerReal_mono (offsetLaw F)
  rintro M ⟨g, hg⟩
  exact ⟨g, hg.trans (Nat.cast_le.mpr (oppositeFailures_card_le_witnesses M g))⟩

theorem oppositeFailures_moment_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m s : ℕ) (hD : D.card ≤ m) :
    (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
      ((oppositeFailures M g).card : ℝ)^s) ≤
        (OppositeAssembly.meanBound (m + (s - 1) * 5))^s := by
  apply (Finset.sum_le_sum (fun M _ =>
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr
        (oppositeFailures_card_le_witnesses M g)) s) ENNReal.toReal_nonneg)).trans
  exact OppositeAssembly.witnesses_moment_le g D a m s hD

theorem tendsto_oppositeFailures_some_large
    (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (K n) |
      ∃ g, Fintype.card (K n) < (oppositeFailures M g).card}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) ?_
    (OppositeTail.tendsto_some_direction_tail K hq)
  intro n
  apply pmf_outerReal_mono (offsetLaw (K n))
  rintro M ⟨g, hg⟩
  refine ⟨g, ?_⟩
  have hq1 : (1 : ℝ) ≤ Fintype.card (K n) := by
    exact_mod_cast Fintype.card_pos (α := K n)
  have hp : (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ) ≤ Fintype.card (K n) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (1 / 100 : ℝ) ≤ 1)
  exact hp.trans ((show (Fintype.card (K n) : ℝ) ≤
    ((oppositeFailures M g).card : ℝ) by exact_mod_cast le_of_lt hg).trans
      (Nat.cast_le.mpr (oppositeFailures_card_le_witnesses M g)))

end
end Balanced.CandidateValidityAssembly

end OAI
