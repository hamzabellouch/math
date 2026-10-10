import OAI.NumberTheory.EgyptianFractions.DivisorFactorBound
import OAI.NumberTheory.EgyptianFractions.WeightedBinomial

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Counting prime-factor sublists, with multiplicities labeled, overcounts divisors. -/
theorem truncatedDivisorCount_le_binomial_of_length (X t : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hlen : ∀ a ∈ n.divisors, (a : ℝ) ≤ X → (a.primeFactorsList.length : ℝ) ≤ t) :
    truncatedDivisorCount X n ≤
      ∑ j ∈ (Finset.range (n.primeFactorsList.length + 1)).filter
          (fun j : ℕ => (j : ℝ) ≤ t), Nat.choose n.primeFactorsList.length j := by
  let S := (Finset.range (n.primeFactorsList.length + 1)).filter
    (fun j : ℕ => (j : ℝ) ≤ t)
  calc
    truncatedDivisorCount X n ≤
        (S.biUnion fun j => (n.primeFactorsList.sublistsLen j).toFinset).card := by
      apply Finset.card_le_card_of_injOn (fun a : ℕ => a.primeFactorsList)
      · intro a ha
        obtain ⟨had, haX⟩ := Finset.mem_filter.mp ha
        have hsub := Nat.primeFactorsList_sublist_of_dvd (Nat.mem_divisors.mp had).1 hn
        apply Finset.mem_biUnion.mpr
        refine ⟨a.primeFactorsList.length, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hsub.length_le; omega),
            hlen a had haX⟩
        · exact List.mem_toFinset.mpr (List.mem_sublistsLen.mpr ⟨hsub, rfl⟩)
      · intro a ha b hb hab
        have ha0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors (Finset.mem_filter.mp ha).1)
        have hb0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1)
        have hp := congrArg List.prod hab
        simpa only [Nat.prod_primeFactorsList ha0, Nat.prod_primeFactorsList hb0] using hp
    _ ≤ ∑ j ∈ S, (n.primeFactorsList.sublistsLen j).toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ j ∈ S, Nat.choose n.primeFactorsList.length j := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [List.length_sublistsLen] using
        List.toFinset_card_le (n.primeFactorsList.sublistsLen j)

private theorem pow_length_le_nat_list_prod (z : ℝ) (hz : 0 ≤ z) (l : List ℕ)
    (hl : ∀ a ∈ l, z ≤ (a : ℝ)) : z ^ l.length ≤ (l.prod : ℝ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : z ≤ (a : ℝ) := hl a (by simp)
    have ht : z ^ l.length ≤ (l.prod : ℝ) := ih (by intro b hb; exact hl b (by simp [hb]))
    simpa only [List.length_cons, List.prod_cons, Nat.cast_mul, pow_succ, mul_comm z] using
      mul_le_mul ha ht (pow_nonneg hz _) (Nat.cast_nonneg a)

/-- If all prime factors are at least z, their number is bounded by log n / log z. -/
theorem primeFactorsList_length_le_log {n : ℕ} (hn : n ≠ 0) {z : ℝ} (hz : 1 < z)
    (hlarge : ∀ p ∈ n.primeFactorsList, z ≤ (p : ℝ)) :
    (n.primeFactorsList.length : ℝ) ≤ Real.log (n : ℝ) / Real.log z := by
  have hz0 : 0 < z := lt_trans zero_lt_one hz
  have hp := pow_length_le_nat_list_prod z hz0.le n.primeFactorsList hlarge
  rw [Nat.prod_primeFactorsList hn] at hp
  apply (le_div_iff₀ (Real.log_pos hz)).2
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos hz0 _) hp

/-- Large prime factors give the standard weighted-binomial divisor bound. -/
theorem truncatedDivisorCount_large_primes_exp (X z q : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hz : 1 < z) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hlarge : ∀ p ∈ n.primeFactorsList, z ≤ (p : ℝ)) :
    (truncatedDivisorCount X n : ℝ) ≤
      Real.exp (-(Real.log X / Real.log z) * Real.log q +
        (n.primeFactorsList.length : ℝ) * q) := by
  apply le_trans _ (weighted_binomial_exp_bound n.primeFactorsList.length
    (Real.log X / Real.log z) q hq0 hq1)
  have hcount := truncatedDivisorCount_le_binomial_of_length X
    (Real.log X / Real.log z) hn (by
      intro a ha haX
      have ha0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
      have hsub := Nat.primeFactorsList_subset_of_dvd (Nat.mem_divisors.mp ha).1 hn
      apply (primeFactorsList_length_le_log ha0 hz (by
        intro p hp; exact hlarge p (hsub hp))).trans
      apply div_le_div_of_nonneg_right _ (Real.log_pos hz).le
      exact Real.log_le_log (by exact_mod_cast Nat.pos_of_mem_divisors ha) haX)
  exact_mod_cast hcount

/-- The large-prime divisor estimate in the entropy form used by the manuscript. -/
theorem truncatedDivisorCount_large_primes_bound (X z W : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hX : 1 < X) (hz : 1 < z) (hXW : Real.log X ≤ W)
    (hnW : Real.log (n : ℝ) ≤ W)
    (hlarge : ∀ p ∈ n.primeFactorsList, z ≤ (p : ℝ)) :
    (truncatedDivisorCount X n : ℝ) ≤
      Real.exp ((1 + Real.log (W / Real.log X)) * Real.log X / Real.log z) := by
  have hv : 0 < Real.log X := Real.log_pos hX
  have hW : 0 < W := lt_of_lt_of_le hv hXW
  have hlz : 0 < Real.log z := Real.log_pos hz
  have hq0 : 0 < Real.log X / W := div_pos hv hW
  have hq1 : Real.log X / W ≤ 1 := (div_le_one hW).2 hXW
  apply (truncatedDivisorCount_large_primes_exp X z (Real.log X / W)
    hn hz hq0 hq1 hlarge).trans
  apply Real.exp_le_exp.mpr
  have hlen : (n.primeFactorsList.length : ℝ) ≤ W / Real.log z :=
    (primeFactorsList_length_le_log hn hz hlarge).trans
      (div_le_div_of_nonneg_right hnW hlz.le)
  calc
    _ ≤ -(Real.log X / Real.log z) * Real.log (Real.log X / W) +
        (W / Real.log z) * (Real.log X / W) := by
      linarith [mul_le_mul_of_nonneg_right hlen hq0.le]
    _ = _ := by
      rw [Real.log_div (ne_of_gt hv) (ne_of_gt hW),
        Real.log_div (ne_of_gt hW) (ne_of_gt hv)]
      field_simp
      ring

/-- Splitting off any prefix of the factorization gives the divisor-prefix moment bound. -/
theorem truncatedDivisorCount_prefix_moment_bound (X z W r : ℝ) {n d : ℕ}
    (hn : n ≠ 0) (hd : d ∣ n) (hX : 1 < X) (hz : 1 < z)
    (hXW : Real.log X ≤ W) (hnW : Real.log (n : ℝ) ≤ W) (hr : 0 ≤ r)
    (hlarge : ∀ p ∈ (n / d).primeFactorsList, z ≤ (p : ℝ)) :
    (truncatedDivisorCount X n : ℝ) ^ r ≤ (d.divisors.card : ℝ) ^ r *
      Real.exp (r * ((1 + Real.log (W / Real.log X)) * Real.log X / Real.log z)) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hnpos
  have hquotpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hnpos hd) hdpos
  have hquotW : Real.log ((n / d : ℕ) : ℝ) ≤ W := by
    apply le_trans _ hnW
    apply Real.log_le_log (by exact_mod_cast hquotpos)
    exact_mod_cast Nat.div_le_self n d
  have hbound : (truncatedDivisorCount X n : ℝ) ≤ (d.divisors.card : ℝ) *
      Real.exp ((1 + Real.log (W / Real.log X)) * Real.log X / Real.log z) := by
    calc
      _ ≤ (d.divisors.card : ℝ) * (truncatedDivisorCount X (n / d) : ℝ) := by
        exact_mod_cast truncatedDivisorCount_factor_bound X hd
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (truncatedDivisorCount_large_primes_bound X z W (Nat.ne_of_gt hquotpos)
          hX hz hXW hquotW hlarge) (Nat.cast_nonneg _)
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg _) hbound hr
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.exp_pos _).le, ← Real.exp_mul] at hp
  simpa only [mul_comm r] using hp

end Problem337

end

end OAI
