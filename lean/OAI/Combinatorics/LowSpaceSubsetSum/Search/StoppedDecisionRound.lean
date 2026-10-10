import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionStoppedAcceptance
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedRepresentationTrial
import OAI.Combinatorics.LowSpaceSubsetSum.Search.DecisionRound

namespace OAI

/-! # Repetition of the two actually stopped trial algorithms

Both branches use their shared-budget executions. No solution, mean
deficiency test, or unbounded source computation chooses the runtime branch.
-/

noncomputable section

namespace LowSpaceSubsetSum.StoppedDecision

variable {n : ℕ}

def compressionAccept (I : Instance n) (B : ℕ) : Option (CompressionSetup.TrialHistory n) → Bool :=
  optionAccept ((CompressionData.mk I).stoppedCompressionTrial B)

def representationAccept (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    Option ((canonicalRepresentationData I).zeroSetup.BucketTrialHistory (by omega)) → Bool :=
  optionAccept ((canonicalRepresentationData I).stoppedTrial (by omega)
    (roundLogBudget I (by omega) hscale) B)

def accept (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (B : ℕ) (h : RoundOutcome I hn) : Bool :=
  compressionAccept I B h.1 || representationAccept I hn hscale B h.2

theorem sound (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (B : ℕ) (h : RoundOutcome I hn) (hy : accept I hn hscale B h = true) : Solvable I := by
  simp only [accept, Bool.or_eq_true] at hy
  rcases hy with hc | hr
  · obtain ⟨history, _, hh⟩ := (optionAccept_eq_true _ _).mp hc
    exact (CompressionData.mk I).stoppedCompressionTrial_sound B history hh
  · obtain ⟨history, _, hh⟩ := (optionAccept_eq_true _ _).mp hr
    exact (canonicalRepresentationData I).stoppedTrial_sound (by omega)
      (roundLogBudget I (by omega) hscale) B history hh

private theorem representation_probability (D : RepresentationData n)
    (hn : 180000000 ≤ n) (hsolve : Solvable D.input)
    (hmean : meanDeficiency D.zeroSetup.originalWeights Finset.univ (mixerSize n / 2) <
      (153 / 20000 : ℝ) * n)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ)))
    (hscale : Real.logb 2 (inputScale D.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    1 / (inputScale D.input : ℝ) ^ 110 ≤
      (D.zeroSetup.bucketHistoryCoupling (by omega)).boundedLaw.probability
        (fun o => ∃ h, o = some h ∧ D.stoppedTrial (by omega)
          (roundLogBudget D.input (by omega) hscale) B h = true) := by
  rcases D with ⟨I, mixers, disjoint, card⟩
  obtain ⟨S, hS⟩ := hsolve
  let R : RepresentationSetup n := ⟨I, S, hS, mixers, disjoint, card⟩
  have hp := R.bounded_stopped_probability hn hmean hden hscale B
  dsimp only [R, RepresentationSetup.runtimeSampler, RepresentationSetup.runtimeData] at hp
  convert hp using 1
  congr 1

theorem probability (I : Instance n) (hn : 180000000 ≤ n) (hsolve : Solvable I)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ))) (B : ℕ) :
    1 / (inputScale I : ℝ) ^ 110 ≤
      (roundLaw I hn).probability (fun h => accept I hn hscale B h = true) := by
  let C := CompressionData.mk I
  let D := canonicalRepresentationData I
  let P := fun o => compressionAccept I B o = true
  let Q := fun o => representationAccept I hn hscale B o = true
  by_cases hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency C.weights Finset.univ (compressionHalfSize n)
  · have hp := C.bounded_stoppedCompression_probability B (by omega) hsolve hmean hscale
    have hu : (2 : ℝ) ≤ inputScale I := by
      exact_mod_cast (show 2 ≤ inputScale I by unfold inputScale; omega)
    have hdenom : (8 : ℝ) ≤ (inputScale I : ℝ) ^ 110 :=
      (by norm_num : (8 : ℝ) ≤ 2 ^ 110).trans (pow_le_pow_left₀ (by norm_num) hu _)
    have hprob : 1 / (inputScale I : ℝ) ^ 110 ≤
        (C.sampler (by omega)).boundedLaw.probability P := by
      apply (one_div_le_one_div_of_le (by norm_num) hdenom).trans
      simpa only [P, compressionAccept, optionAccept_eq_true] using hp
    have hprod := FiniteLaw.prod_or_ge_left (C.sampler (by omega)).boundedLaw
      (D.zeroSetup.bucketHistoryCoupling (by omega)).boundedLaw P Q
    apply hprob.trans
    simpa only [roundLaw, accept, Bool.or_eq_true, P, Q, C, D] using hprod
  · have hm : meanDeficiency D.zeroSetup.originalWeights Finset.univ (mixerSize n / 2) <
        (153 / 20000 : ℝ) * n := lt_of_not_ge hmean
    have hp : 1 / (inputScale I : ℝ) ^ 110 ≤
        (D.zeroSetup.bucketHistoryCoupling (by omega)).boundedLaw.probability Q := by
      simpa only [Q, representationAccept, optionAccept_eq_true, D, canonicalRepresentationData] using
        representation_probability D hn hsolve hm hden hscale B
    have hprod := FiniteLaw.prod_or_ge_right (C.sampler (by omega)).boundedLaw
      (D.zeroSetup.bucketHistoryCoupling (by omega)).boundedLaw P Q
    apply hp.trans
    simpa only [roundLaw, accept, Bool.or_eq_true, P, Q, C, D] using hprod

theorem repeated_sound (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (B : ℕ) (draws : Fin (inputScale I ^ 120) → RoundOutcome I hn)
    (hy : repeatAccept (accept I hn hscale B) draws = true) : Solvable I :=
  repeatAccept_sound _ _ (sound I hn hscale B) draws hy

theorem repeated_probability (I : Instance n) (hn : 180000000 ≤ n) (hsolve : Solvable I)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ))) (B : ℕ) :
    (2 / 3 : ℝ) < ((roundLaw I hn).iid (inputScale I ^ 120)).probability
      (fun draws => repeatAccept (accept I hn hscale B) draws = true) :=
  repetition_acceptance_probability _ _ (by unfold inputScale; omega)
    (probability I hn hsolve hscale hden B)

end LowSpaceSubsetSum.StoppedDecision

end

end OAI
