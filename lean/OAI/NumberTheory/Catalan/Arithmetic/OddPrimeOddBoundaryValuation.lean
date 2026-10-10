import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import OAI.NumberTheory.Catalan.Estimates.BoundaryFormulas

namespace OAI


namespace InternalCatalan

theorem factorial_valuation_below_prime_sq {p n : ℕ} (hp : p.Prime)
    (hn : n < p ^ 2) : padicValNat p n.factorial = n / p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValNat_factorial (Nat.log_lt_of_lt_pow' (by decide : 2 ≠ 0) hn)]
  have hI : Finset.Ico 1 2 = {1} := by decide
  simp [hI]

theorem centralBinom_valuation_floor {p l : ℕ} (hp : p.Prime)
    (hl : 2 * l < p ^ 2) :
    padicValNat p ((2 * l).choose l) = (2 * l) / p - 2 * (l / p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hle : l ≤ 2 * l := by omega
  have hsmall : l < p ^ 2 := by omega
  rw [Nat.choose_eq_factorial_div_factorial hle,
    padicValNat.div_of_dvd (Nat.factorial_mul_factorial_dvd_factorial hle),
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    show 2 * l - l = l by omega,
    factorial_valuation_below_prime_sq hp hl,
    factorial_valuation_below_prime_sq hp hsmall]
  omega

theorem centralBinom_valuation_single_carry {p l : ℕ} (hp : p.Prime)
    (hl : 2 * l < p ^ 2) :
    padicValNat p ((2 * l).choose l) = if p ≤ 2 * (l % p) then 1 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValNat_choose (by omega : l ≤ 2 * l)
    (Nat.log_lt_of_lt_pow' (by decide : 2 ≠ 0) hl)]
  have hI : Finset.Ico 1 2 = {1} := by decide
  simp [hI, Finset.filter_singleton, two_mul]
  split_ifs <;> simp

theorem centralBinom_valuation_le_one {p l : ℕ} (hp : p.Prime)
    (hl : 2 * l < p ^ 2) : padicValNat p ((2 * l).choose l) ≤ 1 := by
  rw [centralBinom_valuation_single_carry hp hl]
  split_ifs <;> omega

theorem centralCoeff_odd_prime_valuation (p l : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    padicValRat p (centralCoeff l) = (padicValNat p ((2 * l).choose l) : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
      padicValRat.of_nat, padicValNat_primes hp2]
    norm_num
  have hfour : padicValRat p (4 : ℚ) = 0 := by
    rw [show (4 : ℚ) = (2 : ℚ) ^ 2 by norm_num, padicValRat.pow, htwo]
    norm_num
  have hnum : (((2 * l).choose l : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.centralBinom_pos l))
  unfold centralCoeff
  rw [padicValRat.div hnum (pow_ne_zero _ (by norm_num)),
    padicValRat.of_nat, padicValRat.pow, hfour]
  simp

theorem centralCoeff_odd_prime_single_carry {p l : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hl : 2 * l < p ^ 2) :
    padicValRat p (centralCoeff l) = if p ≤ 2 * (l % p) then 1 else 0 := by
  rw [centralCoeff_odd_prime_valuation p l hp hp2,
    centralBinom_valuation_single_carry hp hl]
  split_ifs <;> norm_num

theorem centralCoeff_odd_prime_nonneg (p l : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    0 ≤ padicValRat p (centralCoeff l) := by
  rw [centralCoeff_odd_prime_valuation p l hp hp2]
  exact Int.natCast_nonneg _

theorem nat_valuation_below_prime_sq {p z : ℕ} (hp : p.Prime)
    (hz0 : z ≠ 0) (hz : z < p ^ 2) :
    padicValNat p z = if z % p = 0 then 1 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hd : z % p = 0
  · rw [ite_eq_left hd]
    have hle := padicValNat_le_nat_log (p := p) z
    have hlog := Nat.log_lt_of_lt_pow' (by decide : 2 ≠ 0) hz
    have hge := one_le_padicValNat_of_dvd hz0 (Nat.dvd_of_mod_eq_zero hd)
    omega
  · rw [ite_eq_right hd]
    exact padicValNat.eq_zero_of_not_dvd (fun h ↦ hd (Nat.mod_eq_zero_of_dvd h))

theorem double_carry_iff_remainder_odd (p l : ℕ) (hp : p % 2 = 1) :
    p ≤ 2 * (l % p) ↔ ((2 * l) % p) % 2 = 1 := by
  have hp0 : 0 < p := by omega
  have hr : l % p < p := Nat.mod_lt l hp0
  rw [← Nat.mul_mod_mod 2 l p]
  by_cases h : p ≤ 2 * (l % p)
  · rw [Nat.mod_eq_sub_mod h,
      Nat.mod_eq_of_lt (show 2 * (l % p) - p < p by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (show 2 * (l % p) < p by omega)]
    omega

theorem boundaryFactor_even_odd_prime_valuation {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzEven : z % 2 = 0) (hz : z < p ^ 2) :
    padicValRat p (boundaryFactor z) = if (z % p) % 2 = 1 then 1 else 0 := by
  have hz2 : 2 * (z / 2) = z := by omega
  have hval := centralCoeff_odd_prime_single_carry hp hp2
    (show 2 * (z / 2) < p ^ 2 by omega)
  have hpar := double_carry_iff_remainder_odd p (z / 2)
    (hp.mod_two_eq_one_iff_ne_two.mpr hp2)
  rw [hz2] at hpar
  rw [boundaryFactor, ite_eq_left hzEven, hval]
  simp only [hpar]

theorem boundaryFactor_even_odd_prime_eq_zero {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzEven : z % 2 = 0) (hz : z < p ^ 2)
    (hrEven : (z % p) % 2 = 0) : padicValRat p (boundaryFactor z) = 0 := by
  rw [boundaryFactor_even_odd_prime_valuation hp hp2 hzEven hz]
  simp [hrEven]

theorem boundaryFactor_even_odd_prime_eq_one {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzEven : z % 2 = 0) (hz : z < p ^ 2)
    (hrOdd : (z % p) % 2 = 1) : padicValRat p (boundaryFactor z) = 1 := by
  rw [boundaryFactor_even_odd_prime_valuation hp hp2 hzEven hz, ite_eq_left hrOdd]

theorem boundaryFactor_even_odd_prime_valuation_of_lt_H {p z H : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzEven : z % 2 = 0)
    (hzH : z < H) (hH : 4 * H < p ^ 2) :
    padicValRat p (boundaryFactor z) = if (z % p) % 2 = 1 then 1 else 0 :=
  boundaryFactor_even_odd_prime_valuation hp hp2 hzEven (by omega)

theorem boundaryFactor_even_mul_odd_prime_valuation {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzEven : z % 2 = 0)
    (hz0 : z ≠ 0) (hz : z < p ^ 2) :
    padicValRat p ((z : ℚ) * boundaryFactor z) =
      if z % p = 0 ∨ (z % p) % 2 = 1 then 1 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast hz0
  rw [padicValRat.mul hzq (boundaryFactor_ne_zero z), padicValRat.of_nat,
    nat_valuation_below_prime_sq hp hz0 hz,
    boundaryFactor_even_odd_prime_valuation hp hp2 hzEven hz]
  by_cases hr : z % p = 0 <;> simp [hr]





open scoped BigOperators

theorem harmonicRat_strictMono (d : ℕ) : StrictMono (harmonicRat d) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [harmonicRat_succ]
  exact lt_add_of_pos_right _ (by positivity)

theorem harmonicRat_sub_ne_zero (d : ℕ) {i j : ℕ} (hij : i ≠ j) :
    harmonicRat d i - harmonicRat d j ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  exact hij ((harmonicRat_strictMono d).injective h)

theorem zetaRat_ne_zero_of_ne {i j : ℕ} (hij : i ≠ j) :
    zetaRat i j ≠ 0 := by
  rw [zetaRat_of_ne hij]
  apply div_ne_zero (harmonicRat_sub_ne_zero 1 hij)
  apply sub_ne_zero.mpr
  intro h
  exact hij (Nat.cast_injective h)

private theorem harmonic_sum_prime_valuation_lower {p : ℕ} [Fact p.Prime]
    {α : Type*} (s : Finset α) (f : α → ℚ)
    (B : ℤ) (hB : B ≤ 0) (hf : ∀ x ∈ s, B ≤ padicValRat p (f x)) :
    B ≤ padicValRat p (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    by_cases hz : f a + ∑ x ∈ s, f x = 0
    · simpa [hz] using hB
    · apply le_trans _ (padicValRat.min_le_padicValRat_add hz)
      apply le_min
      · exact hf a (Finset.mem_insert_self a s)
      · exact ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))

theorem harmonicRat_prime_sq_lower {p n : ℕ} (hp : p.Prime)
    (hn : n < p ^ 2) (d : ℕ) : -(d : ℤ) ≤ padicValRat p (harmonicRat d n) := by
  have : Fact p.Prime := ⟨hp⟩
  unfold harmonicRat
  apply harmonic_sum_prime_valuation_lower
  · omega
  · intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hval : padicValNat p (k + 1) ≤ 1 := by
      rw [nat_valuation_below_prime_sq hp (by omega) (by omega)]
      split_ifs <;> omega
    have hval' : (padicValNat p (k + 1) : ℤ) ≤ 1 := by exact_mod_cast hval
    simp only [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
    have hmul := mul_le_mul_of_nonneg_left hval' (by positivity : 0 ≤ (d : ℤ))
    simpa only [mul_one] using neg_le_neg hmul

private theorem nat_sub_not_dvd_of_mod_ne {p i j : ℕ} (hji : j ≤ i)
    (hres : i % p ≠ j % p) : ¬p ∣ i - j := by
  intro hdiv
  have hzero : (i - j) % p = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have heq : i = (i - j) + j := by omega
  apply hres
  rw [heq, Nat.add_mod, hzero, zero_add, Nat.mod_mod]

theorem sub_natCast_valuation_of_mod_ne {p i j : ℕ}
    (hres : i % p ≠ j % p) : padicValRat p ((i : ℚ) - (j : ℚ)) = 0 := by
  rcases le_total j i with hji | hij
  · rw [← Nat.cast_sub hji, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (nat_sub_not_dvd_of_mod_ne hji hres)]
    norm_num
  · have heq : (i : ℚ) - (j : ℚ) = -((j - i : ℕ) : ℚ) := by
      rw [Nat.cast_sub hij]
      ring
    rw [heq, padicValRat.neg, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (nat_sub_not_dvd_of_mod_ne hij (Ne.symm hres))]
    norm_num

theorem zetaRat_distinct_residue_valuation_lower {p i j : ℕ} (hp : p.Prime)
    (hi : i < p ^ 2) (hj : j < p ^ 2) (hres : i % p ≠ j % p) :
    -1 ≤ padicValRat p (zetaRat i j) := by
  have : Fact p.Prime := ⟨hp⟩
  have hij : i ≠ j := fun h => hres (congrArg (fun n => n % p) h)
  have hnum := harmonicRat_sub_ne_zero 1 hij
  have hden : (i : ℚ) - (j : ℚ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact hij (Nat.cast_injective h)
  have hival : -1 ≤ padicValRat p (harmonicRat 1 i) := by
    simpa using harmonicRat_prime_sq_lower hp hi 1
  have hjval : -1 ≤ padicValRat p (harmonicRat 1 j) := by
    simpa using harmonicRat_prime_sq_lower hp hj 1
  have hsum := padicValRat.min_le_padicValRat_add (p := p)
    (q := harmonicRat 1 i) (r := -harmonicRat 1 j)
    (by simpa only [sub_eq_add_neg] using hnum)
  rw [← sub_eq_add_neg, padicValRat.neg] at hsum
  rw [zetaRat_of_ne hij, padicValRat.div hnum hden,
    sub_natCast_valuation_of_mod_ne hres, sub_zero]
  exact (le_min hival hjval).trans hsum

theorem zetaRat_distinct_residue_scaled_valuation {p i j : ℕ} (hp : p.Prime)
    (hi : i < p ^ 2) (hj : j < p ^ 2) (hres : i % p ≠ j % p) :
    1 ≤ padicValRat p ((p : ℚ) ^ 2 * zetaRat i j) := by
  have : Fact p.Prime := ⟨hp⟩
  have hij : i ≠ j := fun h => hres (congrArg (fun n => n % p) h)
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [padicValRat.mul (pow_ne_zero _ hpq) (zetaRat_ne_zero_of_ne hij),
    padicValRat.pow, padicValRat.self hp.one_lt]
  have hz := zetaRat_distinct_residue_valuation_lower hp hi hj hres
  omega

theorem rational_residue_zero_of_positive_valuation {p : ℕ} [hp : Fact p.Prime]
    {q : ℚ} (hv : 0 < padicValRat p q) :
    (q.den : ZMod p) ≠ 0 ∧ (q.num : ZMod p) / (q.den : ZMod p) = 0 := by
  have hnumval : padicValInt p q.num ≠ 0 := by
    rw [padicValRat_def] at hv
    omega
  have hdenval : padicValNat p q.den = 0 :=
    (Rat.num_or_den_zero_padicVal q hp.out).resolve_left hnumval
  have hdnot : ¬p ∣ q.den := by
    intro hdiv
    have hge := one_le_padicValNat_of_dvd q.den_ne_zero hdiv
    omega
  have hnDiv : (p : ℤ) ∣ q.num := by
    by_contra hn
    exact hnumval (padicValInt.eq_zero_of_not_dvd hn)
  have hnzero : (q.num : ZMod p) = 0 :=
    (CharP.intCast_eq_zero_iff (ZMod p) p q.num).mpr hnDiv
  refine ⟨?_, ?_⟩
  · exact fun hh => hdnot ((ZMod.natCast_eq_zero_iff q.den p).mp hh)
  · rw [hnzero, zero_div]

theorem zetaRat_distinct_residue_reduction {p i j : ℕ} [hp : Fact p.Prime]
    (hi : i < p ^ 2) (hj : j < p ^ 2) (hres : i % p ≠ j % p) :
    (((p : ℚ) ^ 2 * zetaRat i j).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * zetaRat i j).num : ZMod p) /
        (((p : ℚ) ^ 2 * zetaRat i j).den : ZMod p) = 0 := by
  apply rational_residue_zero_of_positive_valuation
  have h := zetaRat_distinct_residue_scaled_valuation hp.out hi hj hres
  omega

end InternalCatalan



namespace InternalCatalan

open scoped BigOperators

theorem prime_sum_valuation_lower {p : ℕ} [Fact p.Prime] {α : Type*}
    (s : Finset α) (f : α → ℚ) (B : ℤ) (hB : B ≤ 0)
    (hf : ∀ x ∈ s, B ≤ padicValRat p (f x)) :
    B ≤ padicValRat p (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    by_cases hz : f a + ∑ x ∈ s, f x = 0
    · simpa [hz] using hB
    · apply le_trans _ (padicValRat.min_le_padicValRat_add hz)
      exact le_min (hf a (Finset.mem_insert_self a s))
        (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))

theorem prime_sub_valuation_lower {p : ℕ} [Fact p.Prime]
    (a b : ℚ) (B : ℤ) (hB : B ≤ 0)
    (ha : B ≤ padicValRat p a) (hb : B ≤ padicValRat p b) :
    B ≤ padicValRat p (a - b) := by
  by_cases hz : a - b = 0
  · simpa [hz] using hB
  · have h := padicValRat.min_le_padicValRat_add (p := p)
      (q := a) (r := -b) (by simpa only [sub_eq_add_neg] using hz)
    rw [← sub_eq_add_neg, padicValRat.neg] at h
    exact (le_min ha hb).trans h

theorem prime_mul_valuation_lower {p : ℕ} [Fact p.Prime]
    (a b : ℚ) (A B : ℤ) (hAB : A + B ≤ 0)
    (ha : A ≤ padicValRat p a) (hb : B ≤ padicValRat p b) :
    A + B ≤ padicValRat p (a * b) := by
  by_cases haz : a = 0
  · simpa [haz] using hAB
  by_cases hbz : b = 0
  · simpa [hbz] using hAB
  rw [padicValRat.mul haz hbz]
  exact add_le_add ha hb

theorem prime_div_nat_valuation_lower {p : ℕ} [Fact p.Prime]
    (a : ℚ) (z H : ℕ) (A : ℤ) (hA : A ≤ 0) (hz : z ≤ H)
    (ha : A ≤ padicValRat p a) :
    A - (Nat.log p H : ℤ) ≤ padicValRat p (a / (z : ℚ)) := by
  by_cases haz : a = 0
  · simp only [haz, zero_div, padicValRat.zero]
    have : 0 ≤ (Nat.log p H : ℤ) := by positivity
    omega
  by_cases hzz : z = 0
  · simp only [hzz, Nat.cast_zero, div_zero, padicValRat.zero]
    have : 0 ≤ (Nat.log p H : ℤ) := by positivity
    omega
  have hval := (padicValNat_le_nat_log (p := p) z).trans (Nat.log_mono_right hz)
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast hzz
  rw [padicValRat.div haz hzq, padicValRat.of_nat]
  omega

theorem centralBinom_prime_valuation_le_log {p : ℕ} [Fact p.Prime] (l : ℕ) :
    padicValNat p ((2 * l).choose l) ≤ Nat.log p (2 * l) := by
  rw [padicValNat_choose (p := p) (by omega : l ≤ 2 * l)
    (by omega : Nat.log p (2 * l) < Nat.log p (2 * l) + 1)]
  calc
    _ ≤ (Finset.Ico 1 (Nat.log p (2 * l) + 1)).card := Finset.card_filter_le _ _
    _ = Nat.log p (2 * l) := by simp

theorem centralCoeff_odd_prime_log_bounds {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (l H : ℕ) (hl : 2 * l ≤ H) :
    0 ≤ padicValRat p (centralCoeff l) ∧
      padicValRat p (centralCoeff l) ≤ (Nat.log p H : ℤ) := by
  rw [centralCoeff_odd_prime_valuation p l hp.out hp2]
  constructor
  · positivity
  · exact_mod_cast (centralBinom_prime_valuation_le_log (p := p) l).trans
      (Nat.log_mono_right hl)

end InternalCatalan



namespace InternalCatalan

open scoped BigOperators

theorem harmonicRat_prime_digit_error (p d n : ℕ) (hp : 0 < p) :
    (p : ℚ) ^ d * harmonicRat d n - harmonicRat d (n / p) =
      ∑ k ∈ Finset.range n,
        if p ∣ k + 1 then 0 else (p : ℚ) ^ d / (((k + 1 : ℕ) : ℚ) ^ d) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hdiv : p ∣ n + 1
    · have hfactor : n + 1 = p * (n / p + 1) := by
        rw [← Nat.succ_div_of_dvd hdiv]
        exact (Nat.mul_div_cancel' hdiv).symm
      have hfactorq : ((n + 1 : ℕ) : ℚ) = (p : ℚ) * ((n / p + 1 : ℕ) : ℚ) := by
        exact_mod_cast hfactor
      have hq : ((n / p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hterm : (p : ℚ) ^ d * (1 / (((n + 1 : ℕ) : ℚ) ^ d)) =
          1 / (((n / p + 1 : ℕ) : ℚ) ^ d) := by
        rw [hfactorq, mul_pow]
        field_simp [hpq, hq]
      rw [harmonicRat_succ, Nat.succ_div_of_dvd hdiv,
        harmonicRat_succ, Finset.sum_range_succ, ite_eq_left hdiv]
      calc
        (p : ℚ) ^ d * (harmonicRat d n + 1 / (((n + 1 : ℕ) : ℚ) ^ d)) -
            (harmonicRat d (n / p) + 1 / (((n / p + 1 : ℕ) : ℚ) ^ d)) =
          ((p : ℚ) ^ d * harmonicRat d n - harmonicRat d (n / p)) +
            ((p : ℚ) ^ d * (1 / (((n + 1 : ℕ) : ℚ) ^ d)) -
              1 / (((n / p + 1 : ℕ) : ℚ) ^ d)) := by ring
        _ = _ := by rw [ih, hterm]; ring
    · rw [harmonicRat_succ, Nat.succ_div_of_not_dvd hdiv,
        Finset.sum_range_succ, ite_eq_right hdiv]
      calc
        (p : ℚ) ^ d * (harmonicRat d n + 1 / (((n + 1 : ℕ) : ℚ) ^ d)) -
            harmonicRat d (n / p) =
          ((p : ℚ) ^ d * harmonicRat d n - harmonicRat d (n / p)) +
            (p : ℚ) ^ d / (((n + 1 : ℕ) : ℚ) ^ d) := by ring
        _ = _ := by rw [ih]

private theorem finite_sum_valuation_zero_or_one_le {p : ℕ} [Fact p.Prime]
    (s : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ k ∈ s, f k = 0 ∨ 1 ≤ padicValRat p (f k)) :
    (∑ k ∈ s, f k) = 0 ∨ 1 ≤ padicValRat p (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have has := hf a (Finset.mem_insert_self a s)
    have hss := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    rcases has with haz | hav
    · simpa only [haz, zero_add] using hss
    · rcases hss with hsz | hsv
      · right
        simpa only [hsz, add_zero] using hav
      · by_cases hzero : f a + ∑ k ∈ s, f k = 0
        · exact Or.inl hzero
        · exact Or.inr ((le_min hav hsv).trans (padicValRat.min_le_padicValRat_add hzero))

theorem harmonicRat_prime_digit_error_valuation {p n d : ℕ}
    (hp : p.Prime) (hd : 0 < d) :
    (p : ℚ) ^ d * harmonicRat d n - harmonicRat d (n / p) = 0 ∨
      1 ≤ padicValRat p ((p : ℚ) ^ d * harmonicRat d n - harmonicRat d (n / p)) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [harmonicRat_prime_digit_error p d n hp.pos]
  apply finite_sum_valuation_zero_or_one_le
  intro k _
  by_cases hk : p ∣ k + 1
  · exact Or.inl (ite_eq_left hk)
  · right
    rw [ite_eq_right hk]
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hkq : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [padicValRat.div (pow_ne_zero d hpq) (pow_ne_zero d hkq),
      padicValRat.pow, padicValRat.pow, padicValRat.self hp.one_lt,
      padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hk]
    simpa using (show 1 ≤ (d : ℤ) by omega)

end InternalCatalan



namespace InternalCatalan

theorem two_odd_prime_valuation {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    padicValRat p (2 : ℚ) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
    padicValRat.of_nat, padicValNat_primes hp2]
  norm_num

theorem boundaryFactor_odd_prime_log_bounds {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (z H : ℕ) (hz : z ≤ H) :
    -2 * (Nat.log p H : ℤ) ≤ padicValRat p (boundaryFactor z) ∧
      padicValRat p (boundaryFactor z) ≤ (Nat.log p H : ℤ) := by
  have hlog : 0 ≤ (Nat.log p H : ℤ) := by positivity
  by_cases he : z % 2 = 0
  · have hpair : z = 2 * (z / 2) := by omega
    rw [boundaryFactor, ite_eq_left he]
    have hc := centralCoeff_odd_prime_log_bounds hp2 (z / 2) H (by omega)
    constructor <;> omega
  · have hz0 : (z : ℚ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
    have hc := centralCoeff_odd_prime_log_bounds hp2 ((z - 1) / 2) H (by omega)
    have hzval : (padicValNat p z : ℤ) ≤ (Nat.log p H : ℤ) := by
      exact_mod_cast (padicValNat_le_nat_log (p := p) z).trans (Nat.log_mono_right hz)
    rw [boundaryFactor, ite_eq_right he, one_div, padicValRat.inv,
      padicValRat.mul hz0 (centralCoeff_ne_zero _), padicValRat.of_nat]
    constructor <;> omega

theorem momentScalar_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i H : ℕ) (hi : i < H) :
    -2 * (Nat.log p H : ℤ) ≤ padicValRat p (momentScalar i) := by
  have hlog : 0 ≤ (Nat.log p H : ℤ) := by positivity
  by_cases he : i % 2 = 0
  · have hi0 : ((i + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hc := centralCoeff_odd_prime_log_bounds hp2 (i / 2) H (by omega)
    have hiv : (padicValNat p (i + 1) : ℤ) ≤ (Nat.log p H : ℤ) := by
      exact_mod_cast (padicValNat_le_nat_log (p := p) (i + 1)).trans
        (Nat.log_mono_right (by omega : i + 1 ≤ H))
    rw [momentScalar, ite_eq_left he,
      padicValRat.div (by norm_num) (mul_ne_zero hi0 (centralCoeff_ne_zero _)),
      padicValRat.mul hi0 (centralCoeff_ne_zero _),
      two_odd_prime_valuation hp2, padicValRat.of_nat]
    omega
  · simp only [momentScalar, ite_eq_right he, padicValRat.zero]
    omega

theorem boundaryPlusWeight_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z H : ℕ) (hz0 : 0 < z) (hz : z ≤ H) :
    -3 * (Nat.log p H : ℤ) ≤ padicValRat p (boundaryPlusWeight z) := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have hfv := (boundaryFactor_odd_prime_log_bounds hp2 z H hz).2
  have hzv : (padicValNat p z : ℤ) ≤ (Nat.log p H : ℤ) := by
    exact_mod_cast (padicValNat_le_nat_log (p := p) z).trans (Nat.log_mono_right hz)
  rw [boundaryPlusWeight,
    padicValRat.div (by norm_num) (mul_ne_zero (pow_ne_zero _ hzq) (boundaryFactor_ne_zero _)),
    padicValRat.mul (pow_ne_zero _ hzq) (boundaryFactor_ne_zero _),
    padicValRat.pow, padicValRat.of_nat, two_odd_prime_valuation hp2]
  norm_num
  omega

theorem boundaryMinusWeight_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z H : ℕ) (hz0 : 0 < z) (hz : z ≤ H) :
    -4 * (Nat.log p H : ℤ) ≤ padicValRat p (boundaryMinusWeight z) := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have hlog : 0 ≤ (Nat.log p H : ℤ) := by positivity
  have hfv := (boundaryFactor_odd_prime_log_bounds hp2 z H hz).2
  have hzv : (padicValNat p z : ℤ) ≤ (Nat.log p H : ℤ) := by
    exact_mod_cast (padicValNat_le_nat_log (p := p) z).trans (Nat.log_mono_right hz)
  unfold boundaryMinusWeight
  split_ifs
  · rw [padicValRat.div (by norm_num)
      (mul_ne_zero (pow_ne_zero _ hzq) (pow_ne_zero _ (boundaryFactor_ne_zero _))),
      padicValRat.mul (pow_ne_zero _ hzq) (pow_ne_zero _ (boundaryFactor_ne_zero _)),
      padicValRat.pow, padicValRat.pow, padicValRat.of_nat, two_odd_prime_valuation hp2]
    norm_num
    omega
  · rw [padicValRat.div (by norm_num) hzq, two_odd_prime_valuation hp2, padicValRat.of_nat]
    omega





open scoped BigOperators

theorem harmonicRat_prime_log_lower {p : ℕ} [Fact p.Prime] (d n H : ℕ) (hn : n ≤ H) :
    -((d : ℤ) * (Nat.log p H : ℤ)) ≤ padicValRat p (harmonicRat d n) := by
  unfold harmonicRat
  apply prime_sum_valuation_lower
  · have : 0 ≤ (d : ℤ) * (Nat.log p H : ℤ) := by positivity
    omega
  · intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hval : padicValNat p (k + 1) ≤ Nat.log p H :=
      (padicValNat_le_nat_log (p := p) (k + 1)).trans
        (Nat.log_mono_right (by omega : k + 1 ≤ H))
    have hval' : (padicValNat p (k + 1) : ℤ) ≤ (Nat.log p H : ℤ) := by
      exact_mod_cast hval
    simp only [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hval' (by positivity))

private theorem zetaRat_prime_log_lower_of_le {p : ℕ} [Fact p.Prime] (H i j : ℕ)
    (hi : i < H) (hji : j ≤ i) :
    -2 * (Nat.log p H : ℤ) ≤ padicValRat p (zetaRat i j) := by
  have hj : j < H := lt_of_le_of_lt hji hi
  by_cases hij : i = j
  · subst j
    rw [zetaRat_diagonal, padicValRat.neg]
    simpa using harmonicRat_prime_log_lower 2 i H (Nat.le_of_lt hi)
  · have hden : ((i - j : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (show i - j ≠ 0 by omega)
    have heq : (i : ℚ) - (j : ℚ) = ((i - j : ℕ) : ℚ) :=
      (Nat.cast_sub hji).symm
    by_cases hnum : harmonicRat 1 i - harmonicRat 1 j = 0
    · rw [zetaRat_of_ne hij, hnum, zero_div, padicValRat.zero]
      have : 0 ≤ (Nat.log p H : ℤ) := by positivity
      omega
    · have hival : -(Nat.log p H : ℤ) ≤ padicValRat p (harmonicRat 1 i) := by
        simpa using harmonicRat_prime_log_lower 1 i H (Nat.le_of_lt hi)
      have hjval : -(Nat.log p H : ℤ) ≤ padicValRat p (harmonicRat 1 j) := by
        simpa using harmonicRat_prime_log_lower 1 j H (Nat.le_of_lt hj)
      have hsum := padicValRat.min_le_padicValRat_add (p := p)
        (q := harmonicRat 1 i) (r := -harmonicRat 1 j)
        (by simpa only [sub_eq_add_neg] using hnum)
      rw [← sub_eq_add_neg, padicValRat.neg] at hsum
      have hnval : -(Nat.log p H : ℤ) ≤
          padicValRat p (harmonicRat 1 i - harmonicRat 1 j) :=
        (le_min hival hjval).trans hsum
      have hdval : padicValNat p (i - j) ≤ Nat.log p H :=
        (padicValNat_le_nat_log (p := p) (i - j)).trans
          (Nat.log_mono_right (by omega : i - j ≤ H))
      rw [zetaRat_of_ne hij, heq, padicValRat.div hnum hden, padicValRat.of_nat]
      omega

theorem zetaRat_prime_log_lower {p : ℕ} [Fact p.Prime] (H i j : ℕ) (hi : i < H) (hj : j < H) :
    -2 * (Nat.log p H : ℤ) ≤ padicValRat p (zetaRat i j) := by
  rcases le_total j i with hji | hij
  · exact zetaRat_prime_log_lower_of_le H i j hi hji
  · rw [zetaRat_symm]
    exact zetaRat_prime_log_lower_of_le H j i hj hij

end InternalCatalan



namespace InternalCatalan

private theorem prime_sub_valuation_nonneg {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    0 ≤ padicValRat p (a - b) := by
  by_cases hz : a - b = 0
  · simp [hz]
  · have h := padicValRat.min_le_padicValRat_add (p := p)
      (q := a) (r := -b) (by simpa only [sub_eq_add_neg] using hz)
    rw [← sub_eq_add_neg, padicValRat.neg] at h
    exact (le_min ha hb).trans h

private theorem prime_sub_valuation_pos_or_zero {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : a = 0 ∨ 1 ≤ padicValRat p a) (hb : b = 0 ∨ 1 ≤ padicValRat p b) :
    a - b = 0 ∨ 1 ≤ padicValRat p (a - b) := by
  by_cases hz : a - b = 0
  · exact Or.inl hz
  · apply Or.inr
    rcases ha with rfl | ha
    · simpa using hb.resolve_left (by intro h; apply hz; simp [h])
    rcases hb with rfl | hb
    · simpa using ha
    have h := padicValRat.min_le_padicValRat_add (p := p)
      (q := a) (r := -b) (by simpa only [sub_eq_add_neg] using hz)
    rw [← sub_eq_add_neg, padicValRat.neg] at h
    exact (le_min ha hb).trans h

theorem rational_den_ne_zero_of_valuation_nonneg {p : ℕ} [hp : Fact p.Prime]
    {q : ℚ} (hv : 0 ≤ padicValRat p q) : (q.den : ZMod p) ≠ 0 := by
  have hdval : padicValNat p q.den = 0 := by
    rcases Rat.num_or_den_zero_padicVal q hp.out with hn | hd
    · rw [padicValRat_def, hn] at hv
      omega
    · exact hd
  intro hden
  have hdiv := (ZMod.natCast_eq_zero_iff q.den p).mp hden
  have hge := one_le_padicValNat_of_dvd q.den_ne_zero hdiv
  omega

private theorem zero_residue_of_zero_or_positive {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hq : q = 0 ∨ 1 ≤ padicValRat p q) :
    (q.den : ZMod p) ≠ 0 ∧ (q.num : ZMod p) / (q.den : ZMod p) = 0 := by
  rcases hq with rfl | hq
  · norm_num
  · exact rational_residue_zero_of_positive_valuation (by omega)

theorem rational_residue_eq_of_difference {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0)
    (hd : ((a - b).den : ZMod p) ≠ 0)
    (he : ((a - b).num : ZMod p) / ((a - b).den : ZMod p) = 0) :
    (a.num : ZMod p) / (a.den : ZMod p) =
      (b.num : ZMod p) / (b.den : ZMod p) := by
  have hn : ((a - b).num : ZMod p) = 0 := by
    have h := congrArg (fun x : ZMod p => x * ((a - b).den : ZMod p)) he
    simpa only [div_mul_cancel₀ _ hd, zero_mul] using h
  have hc := congrArg (fun z : ℤ => (z : ZMod p)) (Rat.substr_num_den' a b)
  push_cast at hc
  rw [hn, zero_mul, zero_mul] at hc
  have hc' : (a.num : ZMod p) * (b.den : ZMod p) -
      (b.num : ZMod p) * (a.den : ZMod p) = 0 :=
    (mul_eq_zero.mp hc.symm).resolve_right hd
  exact (div_eq_div_iff ha hb).mpr (sub_eq_zero.mp hc')

private theorem zetaRat_prime_sq_lower_of_le {p i j : ℕ} (hp : p.Prime)
    (hi : i < p ^ 2) (hji : j ≤ i) : -2 ≤ padicValRat p (zetaRat i j) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hij : i = j
  · subst j
    rw [zetaRat_diagonal, padicValRat.neg]
    simpa using harmonicRat_prime_sq_lower hp hi 2
  · have hnum := harmonicRat_sub_ne_zero 1 hij
    have hden : ((i - j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show i - j ≠ 0 by omega)
    have hival : -1 ≤ padicValRat p (harmonicRat 1 i) := by
      simpa using harmonicRat_prime_sq_lower hp hi 1
    have hjval : -1 ≤ padicValRat p (harmonicRat 1 j) := by
      simpa using harmonicRat_prime_sq_lower hp (show j < p ^ 2 by omega) 1
    have hsum := padicValRat.min_le_padicValRat_add (p := p)
      (q := harmonicRat 1 i) (r := -harmonicRat 1 j)
      (by simpa only [sub_eq_add_neg] using hnum)
    rw [← sub_eq_add_neg, padicValRat.neg] at hsum
    have hnumval := (le_min hival hjval).trans hsum
    have hdenval : padicValNat p (i - j) ≤ 1 := by
      rw [nat_valuation_below_prime_sq hp (by omega) (by omega)]
      split_ifs <;> omega
    rw [zetaRat_of_ne hij, ← Nat.cast_sub hji, padicValRat.div hnum hden,
      padicValRat.of_nat]
    omega

theorem zetaRat_prime_sq_scaled_valuation_nonneg {p i j : ℕ} (hp : p.Prime)
    (hi : i < p ^ 2) (hj : j < p ^ 2) :
    0 ≤ padicValRat p ((p : ℚ) ^ 2 * zetaRat i j) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hz : zetaRat i j = 0
  · simp [hz]
  · have hval : -2 ≤ padicValRat p (zetaRat i j) := by
      rcases le_total j i with hji | hij
      · exact zetaRat_prime_sq_lower_of_le hp hi hji
      · rw [zetaRat_symm]
        exact zetaRat_prime_sq_lower_of_le hp hj hij
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [padicValRat.mul (pow_ne_zero _ hpq) hz, padicValRat.pow,
      padicValRat.self hp.one_lt]
    omega

private theorem quotients_ne_of_residue_eq {p i j : ℕ} (hij : i ≠ j)
    (hres : i % p = j % p) : i / p ≠ j / p := by
  intro hq
  have hi := Nat.mod_add_div i p
  have hj := Nat.mod_add_div j p
  rw [hres, hq] at hi
  exact hij (hi.symm.trans hj)

private theorem sub_eq_prime_mul_quotient_sub {p i j : ℕ}
    (hres : i % p = j % p) :
    (i : ℚ) - (j : ℚ) =
      (p : ℚ) * (((i / p : ℕ) : ℚ) - ((j / p : ℕ) : ℚ)) := by
  have hi : (i : ℚ) = (i % p : ℚ) + (p : ℚ) * (i / p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div i p).symm
  have hj : (j : ℚ) = (j % p : ℚ) + (p : ℚ) * (j / p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div j p).symm
  rw [hi, hj, hres]
  ring

theorem zetaRat_same_residue_error_identity {p i j : ℕ} (hp : p.Prime)
    (hij : i ≠ j) (hres : i % p = j % p) :
    (p : ℚ) ^ 2 * zetaRat i j - zetaRat (i / p) (j / p) =
      ((p * harmonicRat 1 i - harmonicRat 1 (i / p)) -
        (p * harmonicRat 1 j - harmonicRat 1 (j / p))) /
        (((i / p : ℕ) : ℚ) - ((j / p : ℕ) : ℚ)) := by
  have hq := quotients_ne_of_residue_eq hij hres
  have hd : ((i / p : ℕ) : ℚ) - ((j / p : ℕ) : ℚ) ≠ 0 := by
    exact sub_ne_zero.mpr (fun h => hq (Nat.cast_injective h))
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [zetaRat_of_ne hij, zetaRat_of_ne hq, sub_eq_prime_mul_quotient_sub hres]
  field_simp [hpq, hd]
  ring

theorem zetaRat_same_residue_error_valuation {p i j : ℕ} (hp : p.Prime)
    (hi : i < p ^ 2) (hj : j < p ^ 2) (hres : i % p = j % p) :
    (p : ℚ) ^ 2 * zetaRat i j - zetaRat (i / p) (j / p) = 0 ∨
      1 ≤ padicValRat p ((p : ℚ) ^ 2 * zetaRat i j - zetaRat (i / p) (j / p)) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hij : i = j
  · subst j
    rw [zetaRat_diagonal, zetaRat_diagonal]
    have heq : (p : ℚ) ^ 2 * -harmonicRat 2 i - -harmonicRat 2 (i / p) =
        -((p : ℚ) ^ 2 * harmonicRat 2 i - harmonicRat 2 (i / p)) := by ring
    rw [heq]
    rcases harmonicRat_prime_digit_error_valuation (n := i) hp (by decide : 0 < 2) with hz | hv
    · exact Or.inl (by simp [hz])
    · exact Or.inr (by simpa only [padicValRat.neg] using hv)
  · rw [zetaRat_same_residue_error_identity hp hij hres]
    have hei : (p * harmonicRat 1 i - harmonicRat 1 (i / p) : ℚ) = 0 ∨
        1 ≤ padicValRat p (p * harmonicRat 1 i - harmonicRat 1 (i / p)) := by
      simpa only [pow_one] using
        harmonicRat_prime_digit_error_valuation (n := i) hp (by decide : 0 < 1)
    have hej : (p * harmonicRat 1 j - harmonicRat 1 (j / p) : ℚ) = 0 ∨
        1 ≤ padicValRat p (p * harmonicRat 1 j - harmonicRat 1 (j / p)) := by
      simpa only [pow_one] using
        harmonicRat_prime_digit_error_valuation (n := j) hp (by decide : 0 < 1)
    have hq := quotients_ne_of_residue_eq hij hres
    have hiq : i / p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by simpa [pow_two] using hi)
    have hjq : j / p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by simpa [pow_two] using hj)
    have hd : ((i / p : ℕ) : ℚ) - ((j / p : ℕ) : ℚ) ≠ 0 := by
      exact sub_ne_zero.mpr (fun h => hq (Nat.cast_injective h))
    have hqres : (i / p) % p ≠ (j / p) % p := by
      simpa only [Nat.mod_eq_of_lt hiq, Nat.mod_eq_of_lt hjq] using hq
    have hdval := sub_natCast_valuation_of_mod_ne hqres
    rcases prime_sub_valuation_pos_or_zero hei hej with hz | hv
    · exact Or.inl (by rw [hz, zero_div])
    · apply Or.inr
      have hn : (p * harmonicRat 1 i - harmonicRat 1 (i / p)) -
          (p * harmonicRat 1 j - harmonicRat 1 (j / p)) ≠ 0 := by
        intro h
        rw [h, padicValRat.zero] at hv
        omega
      rw [padicValRat.div hn hd, hdval, sub_zero]
      exact hv

theorem zetaRat_same_residue_reduction {p i j : ℕ} [hp : Fact p.Prime]
    (hi : i < p ^ 2) (hj : j < p ^ 2) (hres : i % p = j % p) :
    (((p : ℚ) ^ 2 * zetaRat i j).den : ZMod p) ≠ 0 ∧
      ((zetaRat (i / p) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * zetaRat i j).num : ZMod p) /
          (((p : ℚ) ^ 2 * zetaRat i j).den : ZMod p) =
            ((zetaRat (i / p) (j / p)).num : ZMod p) /
              ((zetaRat (i / p) (j / p)).den : ZMod p) := by
  let a : ℚ := (p : ℚ) ^ 2 * zetaRat i j
  let b : ℚ := zetaRat (i / p) (j / p)
  have ha : 0 ≤ padicValRat p a := zetaRat_prime_sq_scaled_valuation_nonneg hp.out hi hj
  have he : a - b = 0 ∨ 1 ≤ padicValRat p (a - b) :=
    zetaRat_same_residue_error_valuation hp.out hi hj hres
  have heval : 0 ≤ padicValRat p (a - b) := by
    rcases he with hz | hv
    · simp [hz]
    · omega
  have hb : 0 ≤ padicValRat p b := by
    have h := prime_sub_valuation_nonneg ha heval
    have heq : a - (a - b) = b := by ring
    rwa [heq] at h
  have haden := rational_den_ne_zero_of_valuation_nonneg ha
  have hbden := rational_den_ne_zero_of_valuation_nonneg hb
  have heloc := zero_residue_of_zero_or_positive he
  exact ⟨haden, hbden, rational_residue_eq_of_difference haden hbden heloc.1 heloc.2⟩

theorem zetaRat_prime_digit_reduction {p i j : ℕ} [hp : Fact p.Prime]
    (hi : i < p ^ 2) (hj : j < p ^ 2) :
    (((p : ℚ) ^ 2 * zetaRat i j).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * zetaRat i j).num : ZMod p) /
        (((p : ℚ) ^ 2 * zetaRat i j).den : ZMod p) =
          if i % p = j % p then
            ((zetaRat (i / p) (j / p)).num : ZMod p) /
              ((zetaRat (i / p) (j / p)).den : ZMod p)
          else 0 := by
  by_cases hres : i % p = j % p
  · rw [ite_eq_left hres]
    have h := zetaRat_same_residue_reduction hi hj hres
    exact ⟨h.1, h.2.2⟩
  · rw [ite_eq_right hres]
    exact zetaRat_distinct_residue_reduction hi hj hres





theorem boundaryFactor_odd_prime_valuation {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hzOdd : z % 2 = 1) (hz : z < p ^ 2) :
    padicValRat p (boundaryFactor z) = if (z % p) % 2 = 0 then -1 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hzpos : 0 < z := by omega
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hzpos)
  have hprev : (z - 1) % 2 = 0 := by omega
  have hprevfac : boundaryFactor (z - 1) = centralCoeff ((z - 1) / 2) := by
    rw [boundaryFactor, ite_eq_left hprev]
  have hc : padicValRat p (centralCoeff ((z - 1) / 2)) =
      if ((z - 1) % p) % 2 = 1 then 1 else 0 := by
    rw [← hprevfac]
    exact boundaryFactor_even_odd_prime_valuation hp hp2 hprev (by omega)
  rw [boundaryFactor, ite_eq_right (by omega : z % 2 ≠ 0), one_div,
    padicValRat.inv, padicValRat.mul hzq (centralCoeff_ne_zero _),
    padicValRat.of_nat, nat_valuation_below_prime_sq hp (by omega) hz, hc]
  have hpOdd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hslt : (z - 1) % p < p := Nat.mod_lt _ hp.pos
  have hsucc : z - 1 + 1 = z := by omega
  have hmod := Nat.add_mod (z - 1) 1 p
  rw [hsucc, Nat.mod_eq_of_lt hp.one_lt] at hmod
  by_cases hlast : (z - 1) % p + 1 = p
  · rw [hlast, Nat.mod_self] at hmod
    have hsEven : ((z - 1) % p) % 2 = 0 := by omega
    simp [hmod, hsEven]
  · rw [Nat.mod_eq_of_lt (show (z - 1) % p + 1 < p by omega)] at hmod
    split_ifs <;> omega

theorem boundaryFactor_odd_inverse_valuation_nonneg {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2) :
    0 ≤ padicValRat p (1 / boundaryFactor z) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [one_div, padicValRat.inv, boundaryFactor_odd_prime_valuation hp hp2 hzOdd hz]
  split_ifs <;> norm_num

theorem boundaryFactor_odd_scaled_valuation_nonneg {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2) :
    0 ≤ padicValRat p ((p : ℚ) * boundaryFactor z) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [padicValRat.mul hpq (boundaryFactor_ne_zero z), padicValRat.self hp.one_lt,
    boundaryFactor_odd_prime_valuation hp hp2 hzOdd hz]
  split_ifs <;> norm_num

theorem boundaryFactor_odd_integral_denominators {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2) :
    ((1 / boundaryFactor z).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) * boundaryFactor z).den : ZMod p) ≠ 0 := by
  exact ⟨rational_den_ne_zero_of_valuation_nonneg
      (boundaryFactor_odd_inverse_valuation_nonneg hp.out hp2 hzOdd hz),
    rational_den_ne_zero_of_valuation_nonneg
      (boundaryFactor_odd_scaled_valuation_nonneg hp.out hp2 hzOdd hz)⟩

theorem boundaryFactor_odd_odd_remainder_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2)
    (hrOdd : (z % p) % 2 = 1) :
    (((p : ℚ) * boundaryFactor z).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) * boundaryFactor z).num : ZMod p) /
        (((p : ℚ) * boundaryFactor z).den : ZMod p) = 0 := by
  apply rational_residue_zero_of_positive_valuation
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [padicValRat.mul hpq (boundaryFactor_ne_zero z), padicValRat.self hp.out.one_lt,
    boundaryFactor_odd_prime_valuation hp.out hp2 hzOdd hz]
  norm_num [hrOdd]

end InternalCatalan

end OAI
