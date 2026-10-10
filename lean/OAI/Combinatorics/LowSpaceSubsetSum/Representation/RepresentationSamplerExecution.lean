import OAI.Combinatorics.LowSpaceSubsetSum.Counting.SamplerExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSamplerWork

namespace OAI

/-! # Executed counters for the complete representation sampler -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SamplerExecution

def subset (n k : ℕ) (K : Finset (Fin k)) : Execution (subsetCoupling n k K) :=
  map (permutation n k) (permutationBlock K)

theorem subset_bounded (n k : ℕ) (K : Finset (Fin k)) :
    (subset n k K).Bounded (k * n ^ 3) 0 := map_bounded _ _ (permutation_bounded _ _)

def fixedSize (n g e : ℕ) (he : e ≤ g) : Execution (fixedSizeCoupling n g e he) :=
  map (subset n g (initialSubset g e he)) (initialSubsetEquiv g e he)

theorem fixedSize_bounded (n g e : ℕ) (he : e ≤ g) :
    (fixedSize n g e he).Bounded (g * n ^ 3) 0 := map_bounded _ _ (subset_bounded _ _ _)

def bitArray (n : ℕ) : Execution (bitArrayCoupling n) where
  run bits := ⟨some bits, n, 0⟩
  value_eq _ := rfl

def sign (n : ℕ) : Execution (signCoupling n) := map (bitArray n) (bitsSubsetEquiv n)

theorem sign_bounded (n : ℕ) : (sign n).Bounded n 0 := fun _ => ⟨le_rfl, le_rfl⟩

def factor (n ell : ℕ) : Execution (factorCoupling n ell) :=
  if h : ell < 4 then
    cast (by simp only [factorCoupling, dite_eq_left h]) (map (pure ()) (factorOneEquiv h))
  else cast (by simp only [factorCoupling, dite_eq_right h])
    (map (prime (by omega) n) (factorPrimeEquiv (by omega)))

def primeTestBudget (n : ℕ) : ℕ := n ^ 3 * 2 ^ ((n + 1) / 2)

theorem factor_bounded {n ell : ℕ} (he : ell ≤ n) :
    (factor n ell).Bounded (n ^ 3) (primeTestBudget n) := by
  by_cases h : ell < 4
  · simp only [factor, dite_eq_left h]
    exact cast_bounded _ _
      ((map_bounded _ _ (pure_bounded ())).mono (Nat.zero_le _) (Nat.zero_le _))
  · simp only [factor, dite_eq_right h]
    apply cast_bounded
    apply (map_bounded _ _ (prime_bounded _ _)).mono le_rfl
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))

def triplePrime (n a b c : ℕ) : Execution (triplePrimeCoupling n a b c) :=
  map (prod (prod (factor n a) (factor n b)) (factor n c)) (tripleFactorEquiv a b c)

theorem triplePrime_bounded {n a b c : ℕ} (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) :
    (triplePrime n a b c).Bounded (3 * n ^ 3) (3 * primeTestBudget n) := by
  unfold triplePrime triplePrimeCoupling
  convert map_bounded _ _
    (prod_bounded _ _ (prod_bounded _ _ (factor_bounded ha) (factor_bounded hb))
      (factor_bounded hc)) using 1 <;> ring

end SamplerExecution

namespace SeparatorExpectation.RoundedParameters

variable {g : ℕ} (S : RoundedParameters g)

def samplerExecution (n : ℕ) : SamplerExecution.Execution (S.samplerCoupling n) :=
  SamplerExecution.pi 4 _ _ (fun i =>
    SamplerExecution.pi (S.counts i) _ _
      (fun _ => SamplerExecution.fixedSize n g (S.e i) (S.size_le i)))

theorem samplerExecution_bounded (n : ℕ) :
    (S.samplerExecution n).Bounded (44 * g * 2 ^ g * n ^ 3) 0 := by
  have h := SamplerExecution.pi_bounded 4 _ _
    (fun i => SamplerExecution.pi (S.counts i) _ _
      (fun _ => SamplerExecution.fixedSize n g (S.e i) (S.size_le i)))
    (fun i => S.counts i * (g * n ^ 3)) (fun _ => 0) (fun i => by
      simpa using SamplerExecution.pi_bounded (S.counts i) _ _
        (fun _ => SamplerExecution.fixedSize n g (S.e i) (S.size_le i))
        (fun _ => g * n ^ 3) (fun _ => 0)
        (fun _ => SamplerExecution.fixedSize_bounded n g (S.e i) (S.size_le i)))
  apply h.mono ?_ (by simp)
  calc
    _ = S.rangeCalls * n ^ 3 := by
      simp only [rangeCalls, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := Nat.mul_le_mul_right _ S.rangeCalls_le

end SeparatorExpectation.RoundedParameters

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

private instance guessNonempty (n : ℕ) : Nonempty ↥(guessRange n) :=
  (guessRange_nonempty n).to_subtype

def layoutExecution : SamplerExecution.Execution R.layoutCoupling :=
  SamplerExecution.prod (SamplerExecution.permutation n n) (SamplerExecution.sign n)

theorem layoutExecution_bounded :
    R.layoutExecution.Bounded (n * n ^ 3 + n) 0 := by
  simpa only [layoutExecution, layoutCoupling, Nat.add_zero] using SamplerExecution.prod_bounded _ _
    (SamplerExecution.permutation_bounded n n) (SamplerExecution.sign_bounded n)

def guessesExecution : SamplerExecution.Execution R.guessesCoupling :=
  GuessArrayExecution.execution n

theorem guessesExecution_bounded : R.guessesExecution.Bounded (3 * n ^ 3) 0 := by
  exact GuessArrayExecution.execution_bounded n

def partitionsExecution (z : Layout n) : SamplerExecution.Execution (R.partitionsCoupling z) :=
  SamplerExecution.pi 3 _ _
    (fun i => CanonicalPartition.execution R z i)

theorem partitionsExecution_bounded (z : Layout n) :
    (R.partitionsExecution z).Bounded (3 * mixerSize n * n ^ 3) 0 := by
  have h := SamplerExecution.pi_bounded 3 _ _
    (fun i => CanonicalPartition.execution R z i)
    (fun _ => mixerSize n * n ^ 3) (fun _ => 0)
    (fun i => CanonicalPartition.execution_bounded R z i)
  simpa [partitionsExecution, partitionsCoupling, Nat.mul_assoc] using h

def nestedExecution (z : Layout n) : SamplerExecution.Execution (R.nestedCoupling z) :=
  SamplerExecution.triplePrime n (R.factorExponents z 0) (R.factorExponents z 1)
    (R.factorExponents z 2)

theorem nestedExecution_bounded (z : Layout n) :
    (R.nestedExecution z).Bounded (3 * n ^ 3) (3 * SamplerExecution.primeTestBudget n) :=
  SamplerExecution.triplePrime_bounded (R.factorExponents_le_n z 0)
    (R.factorExponents_le_n z 1) (R.factorExponents_le_n z 2)

def residuesExecution {z : Layout n} (p : R.PrimeSpace z) :
    SamplerExecution.Execution (R.residuesCoupling p) := by
  let : NeZero (prefixModulus p.val 0) := ⟨(prefixModulus_pos p 0).ne'⟩
  let : NeZero (prefixModulus p.val 1) := ⟨(prefixModulus_pos p 1).ne'⟩
  let : NeZero (prefixModulus p.val 2) := ⟨(prefixModulus_pos p 2).ne'⟩
  exact SamplerExecution.prod (SamplerExecution.fin n (prefixModulus p.val 0))
    (SamplerExecution.prod (SamplerExecution.fin n (prefixModulus p.val 1))
      (SamplerExecution.fin n (prefixModulus p.val 2)))

theorem residuesExecution_bounded {z : Layout n} (p : R.PrimeSpace z) :
    (R.residuesExecution p).Bounded (3 * n ^ 3) 0 := by
  let : NeZero (prefixModulus p.val 0) := ⟨(prefixModulus_pos p 0).ne'⟩
  let : NeZero (prefixModulus p.val 1) := ⟨(prefixModulus_pos p 1).ne'⟩
  let : NeZero (prefixModulus p.val 2) := ⟨(prefixModulus_pos p 2).ne'⟩
  unfold residuesExecution residuesCoupling
  convert SamplerExecution.prod_bounded _ _ (SamplerExecution.fin_bounded n _)
    (SamplerExecution.prod_bounded _ _ (SamplerExecution.fin_bounded n _)
      (SamplerExecution.fin_bounded n _)) using 1
  ring

def guessHistoryExecution : SamplerExecution.Execution R.guessHistoryCoupling :=
  SamplerExecution.bind R.layoutExecution _ _ (fun _ => R.guessesExecution)

def partitionHistoryExecution : SamplerExecution.Execution R.partitionHistoryCoupling :=
  SamplerExecution.bind R.guessHistoryExecution _ _ (fun h => R.partitionsExecution h.1)

def primeHistoryExecution : SamplerExecution.Execution R.primeHistoryCoupling :=
  SamplerExecution.bind R.partitionHistoryExecution _ _ (fun h => R.nestedExecution h.1.1)

def trialHistoryExecution : SamplerExecution.Execution R.trialHistoryCoupling :=
  SamplerExecution.bind R.primeHistoryExecution _ _ (fun h => R.residuesExecution h.2)

def extraPrimeExecution (z : Layout n) (hn : 100 ≤ n) :
    SamplerExecution.Execution (R.extraPrimeCoupling z hn) :=
  SamplerExecution.prime (R.extraPrimeParameter_range z hn).1 n

theorem extraPrimeExecution_bounded (z : Layout n) (hn : 100 ≤ n) :
    (R.extraPrimeExecution z hn).Bounded (n ^ 3) (SamplerExecution.primeTestBudget n) := by
  apply (SamplerExecution.prime_bounded (R.extraPrimeParameter_range z hn).1 n).mono le_rfl
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
    (by have := (R.extraPrimeParameter_range z hn).2; omega))

def extraHistoryExecution (hn : 100 ≤ n) :
    SamplerExecution.Execution (R.extraHistoryCoupling hn) :=
  SamplerExecution.bind R.trialHistoryExecution _ _
    (fun h => R.extraPrimeExecution h.1.1.1.1 hn)

def bucketHistoryExecution (hn : 10000 ≤ n) :
    SamplerExecution.Execution (R.bucketHistoryCoupling hn) :=
  SamplerExecution.bind (R.extraHistoryExecution (by omega)) _ _
    (fun h => (separatorParameters h.1.1.1.1.2 (by omega)).samplerExecution n)

theorem bucketHistoryExecution_bounded (hn : 10000 ≤ n) :
    (R.bucketHistoryExecution hn).Bounded R.samplerCandidateBudget
      (4 * SamplerExecution.primeTestBudget n) := by
  have hg := SamplerExecution.bind_bounded R.layoutExecution _ _
    (fun _ => R.guessesExecution) R.layoutExecution_bounded
    (fun _ => R.guessesExecution_bounded)
  have hp := SamplerExecution.bind_bounded R.guessHistoryExecution _ _
    (fun h => R.partitionsExecution h.1) hg (fun h => R.partitionsExecution_bounded h.1)
  have hnested := SamplerExecution.bind_bounded R.partitionHistoryExecution _ _
    (fun h => R.nestedExecution h.1.1) hp (fun h => R.nestedExecution_bounded h.1.1)
  have hr := SamplerExecution.bind_bounded R.primeHistoryExecution _ _
    (fun h => R.residuesExecution h.2) hnested (fun h => R.residuesExecution_bounded h.2)
  have he := SamplerExecution.bind_bounded R.trialHistoryExecution _ _
    (fun h => R.extraPrimeExecution h.1.1.1.1 (by omega))
    hr (fun h => R.extraPrimeExecution_bounded h.1.1.1.1 (by omega))
  have hf := SamplerExecution.bind_bounded (R.extraHistoryExecution (by omega)) _ _
    (fun h => (separatorParameters h.1.1.1.1.2 (by omega)).samplerExecution n) he
    (fun h => (separatorParameters h.1.1.1.1.2 (by omega)).samplerExecution_bounded n)
  unfold bucketHistoryExecution bucketHistoryCoupling
  convert hf using 1 <;> try rfl
  all_goals try unfold samplerCandidateBudget rangeCallBound
  all_goals ring

theorem primeTestBudget_half : (SamplerExecution.primeTestBudget n : ℝ) ≤
    2 * (n : ℝ) ^ 3 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  have hc : (((n + 1) / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 + 1 := by
    have hN : (n + 1) / 2 * 2 ≤ n + 1 := Nat.div_mul_le_self (n + 1) 2
    have hR : (((n + 1) / 2 : ℕ) : ℝ) * 2 ≤ n + 1 := by exact_mod_cast hN
    linarith
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hc
  rw [Real.rpow_add (by norm_num), Real.rpow_one] at hp
  have hp' : (2 : ℝ) ^ ((n + 1) / 2) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) * 2 := by
    simpa only [Real.rpow_natCast] using hp
  unfold SamplerExecution.primeTestBudget
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hp' (show (0 : ℝ) ≤ (n : ℝ) ^ 3 by positivity)]

/-- Every executed sampler history, including an exhausted one, has this
candidate-read plus divisor-test bound. No success event is assumed. -/
theorem bucketHistoryExecution_operations (hn : 10000 ≤ n)
    (s : (R.bucketHistoryCoupling hn).Seed) :
    ((R.bucketHistoryExecution hn).run s).reads +
        ((R.bucketHistoryExecution hn).run s).tests ≤
      128 * (inputScale R.input : ℝ) ^ 4 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  have hcounts := R.bucketHistoryExecution_bounded hn s
  have hC : (R.samplerCandidateBudget : ℝ) ≤
      100 * (inputScale R.input : ℝ) ^ 4 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
    have hN : (R.samplerCandidateBudget : ℝ) ≤
        ((R.samplerCandidateBudget + R.samplerDivisorBudget (Equiv.refl _, ∅) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right R.samplerCandidateBudget
        (R.samplerDivisorBudget (Equiv.refl _, ∅)))
    exact hN.trans (R.sampler_operations_half (Equiv.refl _, ∅) (by omega))
  have hP := primeTestBudget_half (n := n)
  have hu : (1 : ℝ) ≤ inputScale R.input := by
    exact_mod_cast (show 1 ≤ inputScale R.input by unfold inputScale; omega)
  have hnU : (n : ℝ) ≤ inputScale R.input := by
    exact_mod_cast (show n ≤ inputScale R.input by unfold inputScale; omega)
  have hn3 : (n : ℝ) ^ 3 ≤ (inputScale R.input : ℝ) ^ 4 :=
    (pow_le_pow_left₀ (by positivity) hnU 3).trans
      (pow_le_pow_right₀ hu (by omega : 3 ≤ 4))
  have hr : (((R.bucketHistoryExecution hn).run s).reads : ℝ) ≤ R.samplerCandidateBudget :=
    by exact_mod_cast hcounts.1
  have ht : (((R.bucketHistoryExecution hn).run s).tests : ℝ) ≤
      4 * (SamplerExecution.primeTestBudget n : ℝ) := by exact_mod_cast hcounts.2
  have he := mul_le_mul_of_nonneg_right hn3
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((n : ℝ) / 2))
  nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((n : ℝ) / 2),
    mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ inputScale R.input by positivity) 4)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((n : ℝ) / 2))]

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
