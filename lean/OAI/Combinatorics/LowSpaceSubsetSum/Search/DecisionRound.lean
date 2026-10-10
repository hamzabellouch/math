import OAI.Combinatorics.LowSpaceSubsetSum.Storage.CanonicalMixers
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionBoundedTrial
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationRuntimeAcceptance
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationDomainSoundness
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FiniteRepetition

namespace OAI

/-! # Input-only rounds and the mean-deficiency dichotomy

Each round samples and runs compression followed by representation. The
analysis chooses which trial supplies its success probability; the program
does not compute mean deficiency. The runtime target is always the original
target, and sampler exhaustion rejects only that trial.

-/

noncomputable section

namespace LowSpaceSubsetSum

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem roundLogBudget (I : Instance n) (hn : 10000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000) :
    Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000 :=
  representation_log_budget hn
    (by exact_mod_cast (show mixerSize n + 1 ≤ inputScale I by
      unfold inputScale mixerSize; omega)) hscale

abbrev RoundOutcome (I : Instance n) (hn : 180000000 ≤ n) :=
  Option (CompressionSetup.TrialHistory n) ×
    Option ((canonicalRepresentationData I).zeroSetup.BucketTrialHistory (by omega))

def roundLaw (I : Instance n) (hn : 180000000 ≤ n) : FiniteLaw (RoundOutcome I hn) :=
  ((CompressionData.mk I).sampler (by omega)).boundedLaw.prod
    (((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling (by omega)).boundedLaw)

def roundCompressionAccept (I : Instance n) (B : ℕ) :
    Option (CompressionSetup.TrialHistory n) → Bool :=
  optionAccept (fun h => (CompressionData.mk I).compressionTrial B h.1 h.2)

def roundRepresentationAccept (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    Option ((canonicalRepresentationData I).zeroSetup.BucketTrialHistory (by omega)) → Bool :=
  optionAccept ((canonicalRepresentationData I).sampledTrial (by omega)
    (roundLogBudget I (by omega) hscale) B)

def roundAccept (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (B : ℕ) (h : RoundOutcome I hn) : Bool :=
  roundCompressionAccept I B h.1 || roundRepresentationAccept I hn hscale B h.2

private theorem input_representation_acceptance (D : RepresentationData n)
    (hn : 180000000 ≤ n) (hsolve : Solvable D.input)
    (hmean : meanDeficiency D.zeroSetup.originalWeights Finset.univ (mixerSize n / 2) <
      (153 / 20000 : ℝ) * n)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ)))
    (hscale : Real.logb 2 (inputScale D.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    1 / (inputScale D.input : ℝ) ^ 110 ≤
      (D.zeroSetup.bucketHistoryCoupling (by omega)).boundedLaw.probability
        (fun o => ∃ h, o = some h ∧ D.sampledTrial (by omega)
          (roundLogBudget D.input (by omega) hscale) B h = true) := by
  rcases D with ⟨I, mixers, disjoint, card⟩
  obtain ⟨S, hS⟩ := hsolve
  let R : RepresentationSetup n := ⟨I, S, hS, mixers, disjoint, card⟩
  have hp := R.bounded_runtime_acceptance_probability hn hmean hden hscale B
  dsimp only [R, RepresentationSetup.runtimeSampler, RepresentationSetup.runtimeData] at hp
  convert hp using 1
  congr 1

theorem roundAccept_sound (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (B : ℕ) (h : RoundOutcome I hn) (hyes : roundAccept I hn hscale B h = true) :
    Solvable I := by
  simp only [roundAccept, Bool.or_eq_true] at hyes
  rcases hyes with hcomp | hrep
  · obtain ⟨x, _, hx⟩ := (optionAccept_eq_true _ _).mp hcomp
    exact (CompressionData.mk I).compressionTrial_sound B x.1 x.2 hx
  · obtain ⟨x, _, hx⟩ := (optionAccept_eq_true _ _).mp hrep
    exact (canonicalRepresentationData I).trial_sound x.1.1.1 x.1.1.2
      (by omega) (roundLogBudget I (by omega) hscale) x.1.2.val
      (primeRange_prime x.1.2.property).pos B (SeparatorCheck.sampledFamilies x.2) hx

theorem round_acceptance_probability (I : Instance n) (hn : 180000000 ≤ n)
    (hsolve : Solvable I)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ))) (B : ℕ) :
    1 / (inputScale I : ℝ) ^ 110 ≤
      (roundLaw I hn).probability (fun h => roundAccept I hn hscale B h = true) := by
  let C := CompressionData.mk I
  let D := canonicalRepresentationData I
  let P := fun o => roundCompressionAccept I B o = true
  let Q := fun o => roundRepresentationAccept I hn hscale B o = true
  by_cases hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency C.weights Finset.univ (compressionHalfSize n)
  · have hp := C.bounded_compression_acceptance_probability B (by omega) hsolve hmean hscale
    have hprod := FiniteLaw.prod_or_ge_left
      (C.sampler (by omega)).boundedLaw
      (D.zeroSetup.bucketHistoryCoupling (by omega)).boundedLaw P Q
    have hp' : 1 / (inputScale I : ℝ) ^ 110 ≤
        (C.sampler (by omega)).boundedLaw.probability P := by
      simpa only [P, roundCompressionAccept, optionAccept_eq_true] using hp
    apply hp'.trans
    simpa only [roundLaw, roundAccept, Bool.or_eq_true, P, Q, C, D] using hprod
  · have hmean' : meanDeficiency D.zeroSetup.originalWeights Finset.univ (mixerSize n / 2) <
        (153 / 20000 : ℝ) * n := lt_of_not_ge hmean
    have hprod := FiniteLaw.prod_or_ge_right
      (C.sampler (by omega)).boundedLaw
      (D.zeroSetup.bucketHistoryCoupling (by omega)).boundedLaw P Q
    have hp' : 1 / (inputScale I : ℝ) ^ 110 ≤
        (D.zeroSetup.bucketHistoryCoupling (by omega)).boundedLaw.probability Q := by
      simpa only [Q, roundRepresentationAccept, optionAccept_eq_true, D, canonicalRepresentationData] using
        input_representation_acceptance D hn hsolve hmean' hden hscale B
    apply hp'.trans
    simpa only [roundLaw, roundAccept, Bool.or_eq_true, P, Q, C, D] using hprod

theorem repeated_round_sound (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (B : ℕ) (draws : Fin (inputScale I ^ 120) → RoundOutcome I hn)
    (hyes : repeatAccept (roundAccept I hn hscale B) draws = true) : Solvable I :=
  repeatAccept_sound _ _ (roundAccept_sound I hn hscale B) draws hyes

theorem repeated_round_probability (I : Instance n) (hn : 180000000 ≤ n)
    (hsolve : Solvable I)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ))) (B : ℕ) :
    (2 / 3 : ℝ) < ((roundLaw I hn).iid (inputScale I ^ 120)).probability
      (fun draws => repeatAccept (roundAccept I hn hscale B) draws = true) :=
  repetition_acceptance_probability _ _
    (by unfold inputScale; omega) (round_acceptance_probability I hn hsolve hscale hden B)

end LowSpaceSubsetSum

end

end OAI
