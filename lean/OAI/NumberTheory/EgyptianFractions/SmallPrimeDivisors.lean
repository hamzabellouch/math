import OAI.NumberTheory.EgyptianFractions.LargePrimeDivisors

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A number with only small prime factors has few divisors once its logarithm is bounded. -/
theorem divisor_card_small_primes_bound (z W : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hz : 0 ≤ z) (hnW : Real.log (n : ℝ) ≤ W)
    (hsmall : ∀ p ∈ n.primeFactors, (p : ℝ) ≤ z) :
    (n.divisors.card : ℝ) ≤ Real.exp (z * Real.log (1 + W / Real.log 2)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hW0 : 0 ≤ W := le_trans (Real.log_nonneg hn1) hnW
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlen : (n.primeFactorsList.length : ℝ) ≤ W / Real.log 2 := by
    apply (primeFactorsList_length_le_log hn (by norm_num : (1 : ℝ) < 2) ?_).trans
      (div_le_div_of_nonneg_right hnW hlog2.le)
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactorsList hp).two_le
  have hcardNat : n.primeFactors.card ≤ ⌊z⌋₊ := by
    calc
      _ ≤ (Finset.Icc 1 ⌊z⌋₊).card := by
        apply Finset.card_le_card
        intro p hp
        apply Finset.mem_Icc.mpr
        constructor
        · exact (Nat.mem_primeFactors.mp hp).1.pos
        · exact (Nat.le_floor_iff hz).2 (hsmall p hp)
      _ = _ := by simp
  have hcard : (n.primeFactors.card : ℝ) ≤ z :=
    (by exact_mod_cast hcardNat : (n.primeFactors.card : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le hz)
  have hbase : 1 ≤ 1 + W / Real.log 2 := by have := div_nonneg hW0 hlog2.le; linarith
  have hbase0 : 0 < 1 + W / Real.log 2 := lt_of_lt_of_le zero_lt_one hbase
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn, Nat.cast_prod]
      simp
    _ ≤ ∏ p ∈ n.primeFactors, (1 + W / Real.log 2) := by
      apply Finset.prod_le_prod₀
      · intro p hp; positivity
      · intro p hp
        have hexp : (n.factorization p : ℝ) ≤ n.primeFactorsList.length := by
          exact_mod_cast (show n.factorization p ≤ n.primeFactorsList.length by
            rw [← Nat.primeFactorsList_count_eq]
            exact List.count_le_length)
        linarith
    _ = (1 + W / Real.log 2) ^ n.primeFactors.card := by simp
    _ ≤ (1 + W / Real.log 2) ^ z := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hbase hcard
    _ = _ := by rw [Real.rpow_def_of_pos hbase0]; congr 1; ring

/-- Split the factor list at z and combine the small- and large-prime estimates. -/
theorem truncatedDivisorCount_pointwise_exp_bound (X z W : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hX : 1 < X) (hz : 1 < z) (hXW : Real.log X ≤ W)
    (hnW : Real.log (n : ℝ) ≤ W) :
    (truncatedDivisorCount X n : ℝ) ≤
      Real.exp (z * Real.log (1 + W / Real.log 2) +
        (1 + Real.log (W / Real.log X)) * Real.log X / Real.log z) := by
  let a := n.primeFactorsList.filter (fun p : ℕ => (p : ℝ) < z)
  let b := n.primeFactorsList.filter (fun p : ℕ => ¬ (p : ℝ) < z)
  have hab : a.prod * b.prod = n := by
    have h := List.prod_map_filter_mul_prod_map_filter_not
      (fun p : ℕ => (p : ℝ) < z) id n.primeFactorsList
    simpa only [List.map_id, Nat.prod_primeFactorsList hn] using h
  have ha0 : a.prod ≠ 0 := by
    intro ha; rw [ha, zero_mul] at hab; exact hn hab.symm
  have hb0 : b.prod ≠ 0 := by
    intro hb; rw [hb, mul_zero] at hab; exact hn hab.symm
  have had : a.prod ∣ n := ⟨b.prod, hab.symm⟩
  have hbd : b.prod ∣ n := ⟨a.prod, by simpa [mul_comm] using hab.symm⟩
  have haW : Real.log (a.prod : ℝ) ≤ W := by
    apply le_trans _ hnW
    apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero ha0)
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) had
  have hbW : Real.log (b.prod : ℝ) ≤ W := by
    apply le_trans _ hnW
    apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hb0)
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hbd
  have haperm : a.Perm a.prod.primeFactorsList :=
    Nat.primeFactorsList_unique rfl (by
      intro p hp
      exact Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1)
  have hbperm : b.Perm b.prod.primeFactorsList :=
    Nat.primeFactorsList_unique rfl (by
      intro p hp
      exact Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1)
  have hasmall : ∀ p ∈ a.prod.primeFactors, (p : ℝ) ≤ z := by
    intro p hp
    have hpm := Nat.mem_primeFactors.mp hp
    have hpl : p ∈ a.prod.primeFactorsList :=
      (Nat.mem_primeFactorsList_iff_dvd ha0 hpm.1).2 hpm.2.1
    have hpa : p ∈ a := haperm.mem_iff.mpr hpl
    exact (of_decide_eq_true (List.mem_filter.mp hpa).2).le
  have hblarge : ∀ p ∈ b.prod.primeFactorsList, z ≤ (p : ℝ) := by
    intro p hp
    have hpb : p ∈ b := hbperm.mem_iff.mpr hp
    exact le_of_not_gt (of_decide_eq_true (List.mem_filter.mp hpb).2)
  have hquot : n / a.prod = b.prod := by
    rw [← hab, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha0)]
  have hsmall := divisor_card_small_primes_bound z W ha0 (by linarith) haW hasmall
  have hlarge := truncatedDivisorCount_large_primes_bound X z W hb0 hX hz hXW hbW hblarge
  calc
    (truncatedDivisorCount X n : ℝ) ≤ (a.prod.divisors.card : ℝ) *
        (truncatedDivisorCount X b.prod : ℝ) := by
      have h := truncatedDivisorCount_factor_bound X had
      rw [hquot] at h
      exact_mod_cast h
    _ ≤ Real.exp (z * Real.log (1 + W / Real.log 2)) *
        Real.exp ((1 + Real.log (W / Real.log X)) * Real.log X / Real.log z) :=
      mul_le_mul hsmall hlarge (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

/-- Logarithmic version of the elementary small/large-prime split. -/
theorem truncatedDivisorCount_pointwise_log_bound (X z W : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hX : 1 < X) (hz : 1 < z) (hXW : Real.log X ≤ W)
    (hnW : Real.log (n : ℝ) ≤ W) :
    Real.log (truncatedDivisorCount X n : ℝ) ≤
      z * Real.log (1 + W / Real.log 2) +
        (1 + Real.log (W / Real.log X)) * Real.log X / Real.log z := by
  have hpos : 0 < truncatedDivisorCount X n := by
    apply Finset.card_pos.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Nat.mem_divisors.mpr ⟨one_dvd n, hn⟩
    · simpa using hX.le
  have h := Real.log_le_log (by exact_mod_cast hpos)
    (truncatedDivisorCount_pointwise_exp_bound X z W hn hX hz hXW hnW)
  simpa only [Real.log_exp] using h

end Problem337

end

end OAI
