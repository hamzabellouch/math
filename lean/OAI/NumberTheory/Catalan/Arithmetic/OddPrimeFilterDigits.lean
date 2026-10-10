import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.FieldTheory.Finite.Basic
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeOddBoundaryValuation
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeWeight
import OAI.NumberTheory.Catalan.Determinants.RealColumnDeterminant

namespace OAI


namespace InternalCatalan

open scoped BigOperators

private theorem prime_add_integral {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    0 ≤ padicValRat p (a + b) := by
  by_cases h : a + b = 0
  · simp [h]
  · exact (le_min ha hb).trans (padicValRat.min_le_padicValRat_add h)

private theorem prime_sub_integral {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    0 ≤ padicValRat p (a - b) := by
  rw [sub_eq_add_neg]
  exact prime_add_integral ha (by simpa only [padicValRat.neg] using hb)

private theorem prime_mul_integral {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    0 ≤ padicValRat p (a * b) := by
  by_cases hza : a = 0
  · simp [hza]
  by_cases hzb : b = 0
  · simp [hzb]
  rw [padicValRat.mul hza hzb]
  omega

private theorem prime_div_integral {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : padicValRat p b = 0) (hb0 : b ≠ 0) :
    0 ≤ padicValRat p (a / b) := by
  by_cases hz : a = 0
  · simp [hz]
  rw [padicValRat.div hz hb0, hb, sub_zero]
  exact ha

private theorem prime_sum_integral {p : ℕ} [Fact p.Prime] {α : Type*}
    (s : Finset α) (f : α → ℚ) (hf : ∀ a ∈ s, 0 ≤ padicValRat p (f a)) :
    0 ≤ padicValRat p (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact prime_add_integral (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

private theorem prime_nat_den_valuation {p k : ℕ} (hk0 : 0 < k) (hk : k < p) :
    padicValRat p (k : ℚ) = 0 := by
  rw [padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hk0 hk)]
  norm_num

theorem centralCoeff_odd_prime_valuation_zero_of_lt {p l : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hl : 2 * l < p) :
    padicValRat p (centralCoeff l) = 0 := by
  have hsq : 2 * l < p ^ 2 := by nlinarith [hp.two_le]
  have hlp : l < p := by omega
  rw [centralCoeff_odd_prime_single_carry hp hp2 hsq,
    Nat.mod_eq_of_lt hlp, ite_eq_right (by omega : ¬p ≤ 2 * l)]

theorem momentScalar_even_odd_prime_valuation_zero_of_lt {p l : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hl : 2 * l + 1 < p) :
    padicValRat p (momentScalar (2 * l)) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
      padicValRat.of_nat, padicValNat_primes hp2]
    norm_num
  have hden : ((2 * l + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hndvd : ¬p ∣ 2 * l + 1 :=
    Nat.not_dvd_of_pos_of_lt (by omega) hl
  rw [momentScalar_even,
    padicValRat.div (by norm_num) (mul_ne_zero hden (centralCoeff_ne_zero l)),
    padicValRat.mul hden (centralCoeff_ne_zero l), htwo,
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hndvd,
    centralCoeff_odd_prime_valuation_zero_of_lt hp hp2 (by omega)]
  norm_num

theorem momentScalar_odd_prime_valuation_nonneg {p i : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hi : i + 1 < p) :
    0 ≤ padicValRat p (momentScalar i) := by
  by_cases heven : i % 2 = 0
  · have heq : i = 2 * (i / 2) := by omega
    have hv : padicValRat p (momentScalar i) = 0 := by
      rw [heq]
      exact momentScalar_even_odd_prime_valuation_zero_of_lt hp hp2 (by omega)
    exact le_of_eq hv.symm
  · simp [momentScalar, heven]

theorem boundaryMinus_odd_prime_valuation_nonneg {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (n : ℕ) (hn : n < p) : 0 ≤ padicValRat p (boundaryMinus n) := by
  have : Fact p.Prime := ⟨hp⟩
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simpa using (zero_le_padicValRat_of_nat (p := p) 2)
      | succ d =>
        rw [boundaryMinus]
        apply prime_div_integral
        · apply prime_add_integral
          · apply prime_add_integral
            · exact prime_mul_integral (zero_le_padicValRat_of_nat _)
                (ih d (by omega) (by omega))
            · exact momentScalar_odd_prime_valuation_nonneg hp hp2 (by omega)
          · exact momentScalar_odd_prime_valuation_nonneg hp hp2 (by omega)
        · exact prime_nat_den_valuation (by omega) (by omega)
        · positivity

theorem boundaryPlus_odd_prime_valuation_nonneg {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (n : ℕ) (hn : n < p) : 0 ≤ padicValRat p (boundaryPlus n) := by
  have : Fact p.Prime := ⟨hp⟩
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
      padicValRat.of_nat, padicValNat_primes hp2]
    norm_num
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp
      | succ d =>
        rw [boundaryPlus]
        apply prime_div_integral
        · apply prime_add_integral
          · exact prime_mul_integral (zero_le_padicValRat_of_nat _)
              (ih d (by omega) (by omega))
          · exact prime_div_integral (le_of_eq htwo.symm)
              (prime_nat_den_valuation (by omega) (by omega)) (by positivity)
        · exact prime_nat_den_valuation (by omega) (by omega)
        · positivity

theorem momentRat_odd_prime_small_valuation_nonneg {p i j : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hi : i < p) (hj : j < p) :
    0 ≤ padicValRat p (momentRat i j) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hji : j ≤ i
  · rw [momentRat_of_le hji]
    apply prime_sub_integral
    · exact boundaryMinus_odd_prime_valuation_nonneg hp hp2 _ (by omega)
    · apply prime_sum_integral
      intro k hk
      have hk' : k < j := Finset.mem_range.mp hk
      exact prime_div_integral
        (momentScalar_odd_prime_valuation_nonneg hp hp2 (by omega))
        (prime_nat_den_valuation (by omega) (by omega)) (by positivity)
  · rw [momentRat_of_lt (by omega : i < j)]
    apply prime_sub_integral
    · exact boundaryPlus_odd_prime_valuation_nonneg hp hp2 _ (by omega)
    · apply prime_sum_integral
      intro k hk
      have hk' : k < i := Finset.mem_range.mp hk
      exact prime_div_integral
        (momentScalar_odd_prime_valuation_nonneg hp hp2 (by omega))
        (prime_nat_den_valuation (by omega) (by omega)) (by positivity)

theorem momentRat_odd_prime_small_den_ne_zero {p i j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hi : i < p) (hj : j < p) :
    ((momentRat i j).den : ZMod p) ≠ 0 :=
  rational_den_ne_zero_of_valuation_nonneg
    (momentRat_odd_prime_small_valuation_nonneg hp.out hp2 hi hj)

theorem momentRat_odd_prime_small_scaled_reduction {p i j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hi : i < p) (hj : j < p) :
    (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * momentRat i j).num : ZMod p) /
        (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) = 0 := by
  by_cases hz : momentRat i j = 0
  · simp [hz]
  · apply rational_residue_zero_of_positive_valuation
    have hval := momentRat_odd_prime_small_valuation_nonneg hp.out hp2 hi hj
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [padicValRat.mul (pow_ne_zero _ hpq) hz, padicValRat.pow,
      padicValRat.self hp.out.one_lt]
    omega

end InternalCatalan



namespace InternalCatalan

theorem nat_fraction_reduced_residue {p : ℕ} [hp : Fact p.Prime] (n d : ℕ)
    (hd : (d : ZMod p) ≠ 0) :
    (((n : ℚ) / d).den : ZMod p) ≠ 0 ∧
      (((n : ℚ) / d).num : ZMod p) / (((n : ℚ) / d).den : ZMod p) =
        (n : ZMod p) / (d : ZMod p) := by
  let q : ℚ := (n : ℚ) / d
  have hd0 : d ≠ 0 := by intro h; apply hd; simp [h]
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  have hdnot : ¬p ∣ d := fun h => hd ((ZMod.natCast_eq_zero_iff d p).mpr h)
  have hdval : padicValRat p (d : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hdnot]
    norm_num
  have hqval : 0 ≤ padicValRat p q := by
    by_cases hn : n = 0
    · simp [q, hn]
    · have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
      dsimp only [q]
      rw [padicValRat.div hnq hdq, hdval, sub_zero]
      exact zero_le_padicValRat_of_nat n
  have hqd := rational_den_ne_zero_of_valuation_nonneg hqval
  have hqeq : (q.num : ℚ) / (q.den : ℚ) = (n : ℚ) / (d : ℚ) := q.num_div_den
  have hcrossq := (div_eq_div_iff (by exact_mod_cast q.den_ne_zero) hdq).mp hqeq
  have hcrossz : q.num * (d : ℤ) = (n : ℤ) * (q.den : ℤ) := by
    exact_mod_cast hcrossq
  have hcross := congrArg (fun z : ℤ => (z : ZMod p)) hcrossz
  push_cast at hcross
  exact ⟨hqd, (div_eq_div_iff hqd hd).mpr hcross⟩

theorem centralCoeff_reduced_residue {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (l : ℕ) :
    ((centralCoeff l).den : ZMod p) ≠ 0 ∧
      ((centralCoeff l).num : ZMod p) / ((centralCoeff l).den : ZMod p) =
        ((2 * l).choose l : ZMod p) / (4 : ZMod p) ^ l := by
  have hd : ((4 ^ l : ℕ) : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using oddPrimeWeight_four_pow_ne_zero hp.out hp2 l
  simpa only [centralCoeff, Nat.cast_pow, Nat.cast_ofNat] using
    nat_fraction_reduced_residue ((2 * l).choose l) (4 ^ l) hd

theorem centralBinom_residue_digit_no_carry {p l : ℕ} [hp : Fact p.Prime]
    (hl : 2 * (l % p) < p) :
    ((2 * l).choose l : ZMod p) =
      ((2 * (l / p)).choose (l / p) : ZMod p) *
        ((2 * (l % p)).choose (l % p) : ZMod p) := by
  have hmod : (2 * l) % p = 2 * (l % p) := by
    rw [← Nat.mul_mod_mod 2 l p, Nat.mod_eq_of_lt hl]
  have hdiv : (2 * l) / p = 2 * (l / p) := by
    have h := Nat.add_div (a := l) (b := l) hp.out.pos
    simpa [← two_mul, show ¬p ≤ 2 * (l % p) by omega] using h
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := 2 * l) (k := l)
  have hc := (ZMod.natCast_eq_natCast_iff _ _ p).mpr h
  rw [hmod, hdiv, Nat.cast_mul] at hc
  simpa only [mul_comm] using hc

theorem centralCoeff_denominator_digit {p : ℕ} [Fact p.Prime] (l : ℕ) :
    (4 : ZMod p) ^ l = (4 : ZMod p) ^ (l / p) * (4 : ZMod p) ^ (l % p) := by
  calc
    (4 : ZMod p) ^ l = (4 : ZMod p) ^ (l % p + p * (l / p)) := by rw [Nat.mod_add_div]
    _ = (4 : ZMod p) ^ (l % p) * ((4 : ZMod p) ^ p) ^ (l / p) := by
      rw [pow_add, pow_mul]
    _ = _ := by rw [ZMod.pow_card]; ring

theorem centralCoeff_finite_digit_no_carry {p l : ℕ} [Fact p.Prime]
    (hl : 2 * (l % p) < p) :
    ((2 * l).choose l : ZMod p) / (4 : ZMod p) ^ l =
      (((2 * (l / p)).choose (l / p) : ZMod p) / (4 : ZMod p) ^ (l / p)) *
        (((2 * (l % p)).choose (l % p) : ZMod p) / (4 : ZMod p) ^ (l % p)) := by
  rw [centralBinom_residue_digit_no_carry hl, centralCoeff_denominator_digit,
    mul_div_mul_comm]

theorem centralCoeff_digit_no_carry {p l : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hl : 2 * (l % p) < p) :
    ((centralCoeff l).den : ZMod p) ≠ 0 ∧
      ((centralCoeff (l / p)).den : ZMod p) ≠ 0 ∧
        ((centralCoeff (l % p)).den : ZMod p) ≠ 0 ∧
          ((centralCoeff l).num : ZMod p) / ((centralCoeff l).den : ZMod p) =
            (((centralCoeff (l / p)).num : ZMod p) / ((centralCoeff (l / p)).den : ZMod p)) *
              (((centralCoeff (l % p)).num : ZMod p) / ((centralCoeff (l % p)).den : ZMod p)) := by
  have h := centralCoeff_reduced_residue hp2 l
  have hq := centralCoeff_reduced_residue hp2 (l / p)
  have hr := centralCoeff_reduced_residue hp2 (l % p)
  refine ⟨h.1, hq.1, hr.1, ?_⟩
  rw [h.2, hq.2, hr.2]
  exact centralCoeff_finite_digit_no_carry hl





theorem boundaryFactor_even_digit_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzEven : z % 2 = 0) (hrEven : (z % p) % 2 = 0) :
    ((boundaryFactor z).den : ZMod p) ≠ 0 ∧
      ((boundaryFactor (z / p)).den : ZMod p) ≠ 0 ∧
        ((centralCoeff ((z % p) / 2)).den : ZMod p) ≠ 0 ∧
          ((boundaryFactor z).num : ZMod p) / ((boundaryFactor z).den : ZMod p) =
            (((boundaryFactor (z / p)).num : ZMod p) /
              ((boundaryFactor (z / p)).den : ZMod p)) *
                (((centralCoeff ((z % p) / 2)).num : ZMod p) /
                  ((centralCoeff ((z % p) / 2)).den : ZMod p)) := by
  have hz2 : 2 * (z / 2) = z := by omega
  have hc : 2 * ((z / 2) % p) < p := by
    have hiff := double_carry_iff_remainder_odd p (z / 2)
      (hp.out.mod_two_eq_one_iff_ne_two.mpr hp2)
    rw [hz2] at hiff
    have hnot : ¬(z % p) % 2 = 1 := by omega
    exact Nat.lt_of_not_ge (fun h => hnot (hiff.mp h))
  have hmod : z % p = 2 * ((z / 2) % p) := by
    conv_lhs => rw [← hz2]
    rw [← Nat.mul_mod_mod 2 (z / 2) p, Nat.mod_eq_of_lt hc]
  have hdiv : z / p = 2 * ((z / 2) / p) := by
    have h := Nat.add_div (a := z / 2) (b := z / 2) hp.out.pos
    have h' : (2 * (z / 2)) / p = 2 * ((z / 2) / p) := by
      simpa [← two_mul, show ¬p ≤ 2 * ((z / 2) % p) by omega] using h
    simpa only [hz2] using h'
  have hqEven : (z / p) % 2 = 0 := by omega
  have hq : (z / 2) / p = (z / p) / 2 := by omega
  have hr : (z / 2) % p = (z % p) / 2 := by omega
  have hzfac : boundaryFactor z = centralCoeff (z / 2) := by
    rw [boundaryFactor, ite_eq_left hzEven]
  have hqfac : boundaryFactor (z / p) = centralCoeff ((z / p) / 2) := by
    rw [boundaryFactor, ite_eq_left hqEven]
  simpa only [hzfac, hqfac, hq, hr] using centralCoeff_digit_no_carry hp2 hc

theorem boundaryFactor_even_carry_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzEven : z % 2 = 0) (hz : z < p ^ 2)
    (hrOdd : (z % p) % 2 = 1) :
    ((boundaryFactor z).den : ZMod p) ≠ 0 ∧
      ((boundaryFactor z).num : ZMod p) / ((boundaryFactor z).den : ZMod p) = 0 := by
  apply rational_residue_zero_of_positive_valuation
  rw [boundaryFactor_even_odd_prime_eq_one hp.out hp2 hzEven hz hrOdd]
  norm_num





theorem filterCoeffRat_den_one (N v : ℕ) : (filterCoeffRat N v).den = 1 := by
  have hint : filterCoeffRat N v =
      (((-1 : ℤ) ^ v * ((q N).choose v : ℤ) : ℤ) : ℚ) := by
    simp [filterCoeffRat]
  rw [hint, Rat.den_intCast]

theorem filterCoeffRat_reduced_residue {p : ℕ} [Fact p.Prime] (N v : ℕ) :
    ((filterCoeffRat N v).den : ZMod p) ≠ 0 ∧
      ((filterCoeffRat N v).num : ZMod p) / ((filterCoeffRat N v).den : ZMod p) =
        (-1 : ZMod p) ^ v * ((q N).choose v : ZMod p) := by
  have hint : filterCoeffRat N v =
      (((-1 : ℤ) ^ v * ((q N).choose v : ℤ) : ℤ) : ℚ) := by
    simp [filterCoeffRat]
  rw [hint, Rat.den_intCast, Rat.num_intCast]
  simp

theorem filterBinomial_prime_digit {p v : ℕ} [hp : Fact p.Prime] :
    ((4 * p).choose v : ZMod p) =
      if v % p = 0 then ((4 : ℕ).choose (v / p) : ZMod p) else 0 := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := 4 * p) (k := v)
  have hc := (ZMod.natCast_eq_natCast_iff _ _ p).mpr h
  rw [Nat.mul_mod_left, Nat.mul_div_cancel 4 hp.out.pos, Nat.cast_mul] at hc
  by_cases hv : v % p = 0
  · simpa [hv] using hc
  · have hzero : (0 : ℕ).choose (v % p) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simpa [hv, hzero] using hc

theorem filterCoeffRat_prime_digit_reduction {p v : ℕ} [hp : Fact p.Prime] :
    ((filterCoeffRat p v).den : ZMod p) ≠ 0 ∧
      ((filterCoeffRat p v).num : ZMod p) / ((filterCoeffRat p v).den : ZMod p) =
        if v % p = 0 then
          (-1 : ZMod p) ^ (v / p) * ((4 : ℕ).choose (v / p) : ZMod p) else 0 := by
  have hcanon := filterCoeffRat_reduced_residue (p := p) p v
  refine ⟨hcanon.1, ?_⟩
  rw [hcanon.2, q, filterBinomial_prime_digit]
  by_cases hv : v % p = 0
  · have hfactor : v = p * (v / p) := by
      have h := Nat.mod_add_div v p
      rw [hv, zero_add] at h
      exact h.symm
    have hsign : (-1 : ZMod p) ^ v = (-1 : ZMod p) ^ (v / p) := by
      calc
        (-1 : ZMod p) ^ v = (-1 : ZMod p) ^ (p * (v / p)) :=
          congrArg (fun n : ℕ => (-1 : ZMod p) ^ n) hfactor
        _ = ((-1 : ZMod p) ^ p) ^ (v / p) := pow_mul _ _ _
        _ = _ := by rw [ZMod.pow_card]
    rw [ite_eq_left hv, ite_eq_left hv, hsign]
  · rw [ite_eq_right hv, ite_eq_right hv, mul_zero]

end InternalCatalan

end OAI
