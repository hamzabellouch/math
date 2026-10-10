import OAI.Combinatorics.LowSpaceSubsetSum.Search.DecisionRound
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationCoreFavorable

namespace OAI

/-! # Acceptance specification with the full-core budget

The finite-law specification accepts only outcomes whose trial succeeds
within the full-core budget. The interrupting execution refines this
Boolean acceptance predicate.
-/

noncomputable section

namespace LowSpaceSubsetSum

attribute [local instance] Classical.propDecidable

namespace RepresentationData

variable {n : ℕ} (D : RepresentationData n)

def budgetedTrial (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega)) : Bool :=
  D.sampledTrial hn hlog B h && decide
    (D.sampledCoreUnits hn hlog B h ≤ inputScale D.input ^ 410 * 2 ^ ((n + 1) / 2))

theorem budgetedTrial_iff (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega)) :
    D.budgetedTrial hn hlog B h = true ↔ D.CoreFavorable hn hlog B h := by
  simp only [budgetedTrial, Bool.and_eq_true, decide_eq_true_eq, CoreFavorable]
  constructor
  · rintro ⟨ht, hb⟩
    refine ⟨ht, ?_⟩
    exact_mod_cast hb
  · rintro ⟨ht, hb⟩
    refine ⟨ht, ?_⟩
    exact_mod_cast hb

end RepresentationData

namespace BudgetDecision

variable {n : ℕ}

def representationAccept (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    Option ((canonicalRepresentationData I).zeroSetup.BucketTrialHistory (by omega)) → Bool :=
  optionAccept ((canonicalRepresentationData I).budgetedTrial (by omega)
    (roundLogBudget I (by omega) hscale) B)

def accept (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (B : ℕ) (h : RoundOutcome I hn) : Bool :=
  roundCompressionAccept I B h.1 || representationAccept I hn hscale B h.2

private theorem input_representation_acceptance (D : RepresentationData n)
    (hn : 180000000 ≤ n) (hsolve : Solvable D.input)
    (hmean : meanDeficiency D.zeroSetup.originalWeights Finset.univ (mixerSize n / 2) <
      (153 / 20000 : ℝ) * n)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ)))
    (hscale : Real.logb 2 (inputScale D.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    1 / (inputScale D.input : ℝ) ^ 110 ≤
      (D.zeroSetup.bucketHistoryCoupling (by omega)).boundedLaw.probability
        (fun o => ∃ h, o = some h ∧ D.budgetedTrial (by omega)
          (roundLogBudget D.input (by omega) hscale) B h = true) := by
  simp only [D.budgetedTrial_iff]
  rcases D with ⟨I, mixers, disjoint, card⟩
  obtain ⟨S, hS⟩ := hsolve
  let R : RepresentationSetup n := ⟨I, S, hS, mixers, disjoint, card⟩
  have hp := R.bounded_runtime_core_probability hn hmean hden hscale B
  dsimp only [R, RepresentationSetup.runtimeSampler, RepresentationSetup.runtimeData] at hp
  convert hp using 1
  congr 1

theorem sound (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (B : ℕ) (h : RoundOutcome I hn) (hyes : accept I hn hscale B h = true) : Solvable I := by
  apply roundAccept_sound I hn hscale B h
  simp only [roundAccept, Bool.or_eq_true]
  simp only [accept, Bool.or_eq_true] at hyes
  rcases hyes with hcomp | hrep
  · exact Or.inl hcomp
  · obtain ⟨x, hx, hb⟩ := (optionAccept_eq_true _ _).mp hrep
    have ht := ((canonicalRepresentationData I).budgetedTrial_iff _ _ _ x).mp hb
    right
    exact (optionAccept_eq_true _ _).mpr ⟨x, hx, ht.1⟩

theorem acceptance_probability (I : Instance n) (hn : 180000000 ≤ n)
    (hsolve : Solvable I)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ))) (B : ℕ) :
    1 / (inputScale I : ℝ) ^ 110 ≤
      (roundLaw I hn).probability (fun h => accept I hn hscale B h = true) := by
  let C := CompressionData.mk I
  let D := canonicalRepresentationData I
  let P := fun o => roundCompressionAccept I B o = true
  let Q := fun o => representationAccept I hn hscale B o = true
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
    simpa only [roundLaw, accept, Bool.or_eq_true, P, Q, C, D] using hprod
  · have hmean' : meanDeficiency D.zeroSetup.originalWeights Finset.univ (mixerSize n / 2) <
        (153 / 20000 : ℝ) * n := lt_of_not_ge hmean
    have hprod := FiniteLaw.prod_or_ge_right
      (C.sampler (by omega)).boundedLaw
      (D.zeroSetup.bucketHistoryCoupling (by omega)).boundedLaw P Q
    have hp' : 1 / (inputScale I : ℝ) ^ 110 ≤
        (D.zeroSetup.bucketHistoryCoupling (by omega)).boundedLaw.probability Q := by
      simpa only [Q, representationAccept, optionAccept_eq_true, D, canonicalRepresentationData] using
        input_representation_acceptance D hn hsolve hmean' hden hscale B
    apply hp'.trans
    simpa only [roundLaw, accept, Bool.or_eq_true, P, Q, C, D] using hprod

theorem repeated_sound (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (B : ℕ) (draws : Fin (inputScale I ^ 120) → RoundOutcome I hn)
    (hyes : repeatAccept (accept I hn hscale B) draws = true) : Solvable I :=
  repeatAccept_sound _ _ (sound I hn hscale B) draws hyes

theorem repeated_probability (I : Instance n) (hn : 180000000 ≤ n)
    (hsolve : Solvable I)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ))) (B : ℕ) :
    (2 / 3 : ℝ) < ((roundLaw I hn).iid (inputScale I ^ 120)).probability
      (fun draws => repeatAccept (accept I hn hscale B) draws = true) :=
  repetition_acceptance_probability _ _
    (by unfold inputScale; omega) (acceptance_probability I hn hsolve hscale hden B)

end BudgetDecision
end LowSpaceSubsetSum

end

end OAI
