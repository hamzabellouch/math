import OAI.NumberTheory.CubicMoment.Estimates.PrimeIntervalGeometry
import OAI.NumberTheory.CubicMoment.Estimates.PrimeMoebiusExtraction

namespace OAI

/-! Concrete selected-side stopping predicates. Replacing one prime
within its fixed bin leaves every selected-bin surrogate test unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppingPrimeSetTest (s : Finset Eisenstein) (bin : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (j k : ℕ) (Z : ℝ) (r : Eisenstein) : Prop :=
  (∀ p ∈ s, bin p ≤ j) ∧ (primeBin s bin j).card = k ∧
    norm r*primeSurrogate s bin ell/ell j < Z ∧
    Z ≤ norm r*primeSurrogate s bin ell

def stoppingSideTest (bin : Eisenstein → ℕ) (ell : ℕ → ℝ)
    (j k : ℕ) (Z : ℝ) (r d : Eisenstein) : Prop :=
  stoppingPrimeSetTest (primaryPrimeFactors d) bin ell j k Z r

lemma primaryPrimeFactors_prime_mul {p c : Eisenstein} (hp : primaryPrime p)
    (hc : primary c) (hs : Squarefree c) (hpc : ¬p ∣ c) :
    primaryPrimeFactors (p*c) = insert p (primaryPrimeFactors c) := by
  have hpnot : p ∉ primaryPrimeFactors c :=
    fun h => hpc (primaryPrimeFactor_spec hc h).2
  have hprime : ∀ q ∈ insert p (primaryPrimeFactors c), primaryPrime q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact (primaryPrimeFactor_spec hc hq).1
  have h := primaryPrimeFactors_finset_prod (insert p (primaryPrimeFactors c)) hprime
  simpa only [Finset.prod_insert hpnot,primaryPrimeFactors_prod hc hs] using h

lemma stoppingPrimeSetTest_insert_same_bin (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k : ℕ) (Z : ℝ) (r : Eisenstein)
    {p q : Eisenstein} (hp : p ∉ s) (hq : q ∉ s) (hbin : bin p = bin q) :
    stoppingPrimeSetTest (insert p s) bin ell j k Z r ↔
      stoppingPrimeSetTest (insert q s) bin ell j k Z r := by
  have hno : (∀ t ∈ insert p s, bin t ≤ j) ↔ (∀ t ∈ insert q s, bin t ≤ j) := by
    simp only [Finset.forall_mem_insert,hbin]
  simp only [stoppingPrimeSetTest,hno,
    primeSurrogate_insert_same_bin s bin ell hp hq hbin,
    primeBin_card_insert_same_bin s bin hp hq hbin j]

theorem stoppingSideTest_free_prime_same_bin (bin : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (j k : ℕ) (Z : ℝ) (r : Eisenstein)
    {c p q : Eisenstein} (hc : primary c) (hs : Squarefree c)
    (hp : primaryPrime p) (hq : primaryPrime q) (hpc : ¬p ∣ c) (hqc : ¬q ∣ c)
    (hbin : bin p = bin q) :
    stoppingSideTest bin ell j k Z r (p*c) ↔
      stoppingSideTest bin ell j k Z r (q*c) := by
  unfold stoppingSideTest
  rw [primaryPrimeFactors_prime_mul hp hc hs hpc,primaryPrimeFactors_prime_mul hq hc hs hqc]
  exact stoppingPrimeSetTest_insert_same_bin _ bin ell j k Z r
    (fun h => hpc (primaryPrimeFactor_spec hc h).2)
    (fun h => hqc (primaryPrimeFactor_spec hc h).2) hbin

theorem failedStage_free_prime_same_bin (bin : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (h : ℕ) (Q : ℝ) (r : Eisenstein)
    {c p q : Eisenstein} (hc : primary c) (hs : Squarefree c)
    (hp : primaryPrime p) (hq : primaryPrime q) (hpc : ¬p ∣ c) (hqc : ¬q ∣ c)
    (hbin : bin p = bin q) :
    (norm r*primeSurrogate (primeBinPrefix (primaryPrimeFactors (p*c)) bin h) bin ell < Q) ↔
      norm r*primeSurrogate (primeBinPrefix (primaryPrimeFactors (q*c)) bin h) bin ell < Q := by
  rw [primaryPrimeFactors_prime_mul hp hc hs hpc,primaryPrimeFactors_prime_mul hq hc hs hqc,
    primeSurrogate_prefix_insert_same_bin _ bin ell
      (fun hp => hpc (primaryPrimeFactor_spec hc hp).2)
      (fun hq => hqc (primaryPrimeFactor_spec hc hq).2) hbin h]

/-- If the free prime is distinguished, the actual stopping inequalities
are a single norm interval; the selected divisor remains fixed. -/
theorem stoppingSideTest_free_distinguished_interval
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k : ℕ) (Z : ℝ)
    {c : Eisenstein} (hc : c ≠ 0) (d p : Eisenstein)
    (hell : 0 < ell j)
    (hS : 0 < primeSurrogate (primaryPrimeFactors d) bin ell) :
    stoppingSideTest bin ell j k Z (c*p) d ↔
      (∀ q ∈ primaryPrimeFactors d, bin q ≤ j) ∧
      (primeBin (primaryPrimeFactors d) bin j).card = k ∧
      Z/(norm c*primeSurrogate (primaryPrimeFactors d) bin ell) ≤ norm p ∧
      norm p < Z*ell j/(norm c*primeSurrogate (primaryPrimeFactors d) bin ell) := by
  unfold stoppingSideTest stoppingPrimeSetTest
  rw [distinguished_prime_crossing_interval hc hS hell]

lemma failedStage_free_distinguished_interval {c p : Eisenstein} (hc : c ≠ 0)
    {S Q : ℝ} (hS : 0 < S) :
    norm (c*p)*S < Q ↔ norm p < Q/(norm c*S) := by
  rw [norm_mul_eq,lt_div_iff₀ (mul_pos (norm_pos_of_ne_zero hc) hS)]
  ring_nf

/-- The selected-prime role can therefore remove its concrete stopping
predicate on a fixed bin without a multiplicity or a variation loss. -/
theorem sum_stoppingSide_same_bin (S : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k : ℕ) (Z : ℝ) (r : Eisenstein)
    {c p₀ : Eisenstein} (hc : primary c) (hsc : Squarefree c)
    (hp₀ : p₀ ∈ S) (hS : ∀ p ∈ S, primaryPrime p)
    (hcop : ∀ p ∈ S, ¬p ∣ c) (hbin : ∀ p ∈ S, bin p = bin p₀)
    (F : Eisenstein → ℂ) :
    (∑ p ∈ S with stoppingSideTest bin ell j k Z r (p*c), F p) =
      if stoppingSideTest bin ell j k Z r (p₀*c) then ∑ p ∈ S, F p else 0 := by
  rw [Finset.sum_filter]
  by_cases h : stoppingSideTest bin ell j k Z r (p₀*c)
  · rw [ite_eq_left h]
    apply Finset.sum_congr rfl
    intro p hp
    rw [ite_eq_left ((stoppingSideTest_free_prime_same_bin bin ell j k Z r hc hsc
      (hS p hp) (hS p₀ hp₀) (hcop p hp) (hcop p₀ hp₀) (hbin p hp)).mpr h)]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro p hp
    apply ite_eq_right
    intro h'
    exact h ((stoppingSideTest_free_prime_same_bin bin ell j k Z r hc hsc
      (hS p hp) (hS p₀ hp₀) (hcop p hp) (hcop p₀ hp₀) (hbin p hp)).mp h')

end CubicFirstMoment

end

end OAI
