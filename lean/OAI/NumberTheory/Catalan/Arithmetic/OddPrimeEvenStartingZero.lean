import Mathlib.Data.Nat.Choose.Vandermonde
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeFilterDigits

namespace OAI


namespace InternalCatalan

theorem rational_residue_mul {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0) :
    ((a * b).den : ZMod p) ≠ 0 ∧
      ((a * b).num : ZMod p) / ((a * b).den : ZMod p) =
        ((a.num : ZMod p) / (a.den : ZMod p)) *
          ((b.num : ZMod p) / (b.den : ZMod p)) := by
  have hab : ((a * b).den : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ (a * b).den :=
      (ZMod.natCast_eq_zero_iff (a * b).den p).mp hzero
    have hprod : p ∣ a.den * b.den := hdiv.trans (Rat.mul_den_dvd a b)
    have hcast := (ZMod.natCast_eq_zero_iff (a.den * b.den) p).mpr hprod
    exact mul_ne_zero ha hb (by simpa only [Nat.cast_mul] using hcast)
  refine ⟨hab, ?_⟩
  rw [div_mul_div_comm]
  apply (div_eq_div_iff hab (mul_ne_zero ha hb)).mpr
  have hc := congrArg (fun z : ℤ => (z : ZMod p)) (Rat.mul_num_den' a b)
  push_cast at hc
  simpa only [mul_assoc] using hc

theorem rational_residue_inv {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hq : q ≠ 0) (hv : padicValRat p q = 0) :
    ((q⁻¹).den : ZMod p) ≠ 0 ∧
      ((q⁻¹).num : ZMod p) / ((q⁻¹).den : ZMod p) =
        ((q.num : ZMod p) / (q.den : ZMod p))⁻¹ := by
  have hd : (q.den : ZMod p) ≠ 0 :=
    rational_den_ne_zero_of_valuation_nonneg (by omega)
  have hdi : ((q⁻¹).den : ZMod p) ≠ 0 :=
    rational_den_ne_zero_of_valuation_nonneg (by simp [padicValRat.inv, hv])
  refine ⟨hdi, ?_⟩
  have hm := rational_residue_mul hd hdi
  have hprod : ((q.num : ZMod p) / (q.den : ZMod p)) *
      (((q⁻¹).num : ZMod p) / ((q⁻¹).den : ZMod p)) = 1 := by
    simpa [mul_inv_cancel₀ hq] using hm.2.symm
  exact ((mul_eq_one_iff_inv_eq₀ (left_ne_zero_of_mul_eq_one hprod)).mp hprod).symm

theorem rational_residue_nat_mul_eq {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (n m : ℕ) (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0)
    (h : (n : ℚ) * a = (m : ℚ) * b) :
    (n : ZMod p) * ((a.num : ZMod p) / (a.den : ZMod p)) =
      (m : ZMod p) * ((b.num : ZMod p) / (b.den : ZMod p)) := by
  have hna := rational_residue_mul (a := (n : ℚ)) (b := a) (by simp) ha
  have hmb := rational_residue_mul (a := (m : ℚ)) (b := b) (by simp) hb
  have he := congrArg (fun q : ℚ => (q.num : ZMod p) / (q.den : ZMod p)) h
  rw [hna.2, hmb.2] at he
  simpa using he

end InternalCatalan


section

open scoped BigOperators

namespace InternalCatalan

theorem rational_residue_add {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0) :
    ((a + b).den : ZMod p) ≠ 0 ∧
      ((a + b).num : ZMod p) / ((a + b).den : ZMod p) =
        ((a.num : ZMod p) / (a.den : ZMod p)) +
          ((b.num : ZMod p) / (b.den : ZMod p)) := by
  have hab : ((a + b).den : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ (a + b).den :=
      (ZMod.natCast_eq_zero_iff (a + b).den p).mp hzero
    have hprod : p ∣ a.den * b.den := hdiv.trans (Rat.add_den_dvd a b)
    have hcast := (ZMod.natCast_eq_zero_iff (a.den * b.den) p).mpr hprod
    exact mul_ne_zero ha hb (by simpa only [Nat.cast_mul] using hcast)
  refine ⟨hab, ?_⟩
  rw [div_add_div _ _ ha hb]
  apply (div_eq_div_iff hab (mul_ne_zero ha hb)).mpr
  have hc := congrArg (fun z : ℤ => (z : ZMod p)) (Rat.add_num_den' a b)
  push_cast at hc
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hc

theorem rational_residue_sum {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) (hden : ∀ i ∈ s, ((f i).den : ZMod p) ≠ 0) :
    ((∑ i ∈ s, f i).den : ZMod p) ≠ 0 ∧
      ((∑ i ∈ s, f i).num : ZMod p) / ((∑ i ∈ s, f i).den : ZMod p) =
        ∑ i ∈ s, ((f i).num : ZMod p) / ((f i).den : ZMod p) := by
  classical
  revert hden
  induction s using Finset.induction_on with
  | empty => intro hden; simp
  | @insert a s ha ih =>
    intro hden
    have hda : ((f a).den : ZMod p) ≠ 0 := hden a (Finset.mem_insert_self a s)
    have hds : ∀ i ∈ s, ((f i).den : ZMod p) ≠ 0 :=
      fun i hi => hden i (Finset.mem_insert_of_mem hi)
    have hs := ih hds
    have hadd := rational_residue_add hda hs.1
    simpa only [Finset.sum_insert ha, hs.2] using hadd

end InternalCatalan

end


namespace InternalCatalan

open scoped BigOperators

private theorem scaled_two_div_den_ne_zero {p : ℕ} [hp : Fact p.Prime]
    (e : ℕ) {q : ℚ} (hq : q ≠ 0) (hv : padicValRat p q ≤ (e : ℤ)) :
    (((p : ℚ) ^ e * (2 / q)).den : ZMod p) ≠ 0 := by
  apply rational_den_ne_zero_of_valuation_nonneg
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have htwo : 0 ≤ padicValRat p (2 : ℚ) := zero_le_padicValRat_of_nat 2
  rw [← mul_div_assoc,
    padicValRat.div (mul_ne_zero (pow_ne_zero e hpq) (by norm_num)) hq,
    padicValRat.mul (pow_ne_zero e hpq) (by norm_num),
    padicValRat.pow, padicValRat.self hp.out.one_lt, mul_one]
  omega

private theorem parityBoundarySum_scaled_den_ne_zero {p : ℕ} [Fact p.Prime]
    (a : ℚ) (f : ℕ → ℚ) (u : ℕ)
    (hf : ∀ z, 0 < z → z ≤ u → z % 2 = u % 2 → ((a * f z).den : ZMod p) ≠ 0) :
    ((a * parityBoundarySum f u).den : ZMod p) ≠ 0 := by
  have hsum := rational_residue_sum (p := p) (Finset.range (u + 1))
    (fun z => a * (if 0 < z ∧ z % 2 = u % 2 then f z else 0)) (by
      intro z hz
      by_cases hgood : 0 < z ∧ z % 2 = u % 2
      · rw [ite_eq_left hgood]
        exact hf z hgood.1 (by have := Finset.mem_range.mp hz; omega) hgood.2
      · simp [hgood])
  simpa only [parityBoundarySum, Finset.mul_sum] using hsum.1

theorem boundaryPlusWeight_even_scaled_den_ne_zero {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz0 : 0 < z) (hzEven : z % 2 = 0) (hz : z < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryPlusWeight z).den : ZMod p) ≠ 0 := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have hvz : padicValRat p (z : ℚ) = if z % p = 0 then 1 else 0 := by
    rw [padicValRat.of_nat, nat_valuation_below_prime_sq hp.out (by omega) hz]
    split_ifs <;> norm_num
  have hvden : padicValRat p ((z : ℚ) ^ 2 * boundaryFactor z) ≤ 2 := by
    rw [padicValRat.mul (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z),
      padicValRat.pow, hvz, boundaryFactor_even_odd_prime_valuation hp.out hp2 hzEven hz]
    by_cases hr0 : z % p = 0
    · simp [hr0]
    · simp only [ite_eq_right hr0]
      split_ifs <;> norm_num
  exact scaled_two_div_den_ne_zero 2
    (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z)) hvden

theorem boundaryPlusWeight_odd_scaled_den_ne_zero {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2) :
    (((p : ℚ) * boundaryPlusWeight z).den : ZMod p) ≠ 0 := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
  have hvz : padicValRat p (z : ℚ) = if z % p = 0 then 1 else 0 := by
    rw [padicValRat.of_nat, nat_valuation_below_prime_sq hp.out (by omega) hz]
    split_ifs <;> norm_num
  have hvden : padicValRat p ((z : ℚ) ^ 2 * boundaryFactor z) ≤ 1 := by
    rw [padicValRat.mul (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z),
      padicValRat.pow, hvz, boundaryFactor_odd_prime_valuation hp.out hp2 hzOdd hz]
    by_cases hr0 : z % p = 0
    · simp [hr0]
    · simp only [ite_eq_right hr0]
      split_ifs <;> norm_num
  simpa only [pow_one, boundaryPlusWeight] using
    scaled_two_div_den_ne_zero 1
      (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z)) hvden

theorem boundaryMinusWeight_even_scaled_den_ne_zero {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz0 : 0 < z) (hzEven : z % 2 = 0) (hz : z < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryMinusWeight z).den : ZMod p) ≠ 0 := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have hvden : padicValRat p ((z : ℚ) ^ 2 * boundaryFactor z ^ 2) ≤ 2 := by
    rw [← mul_pow, padicValRat.pow,
      boundaryFactor_even_mul_odd_prime_valuation hp.out hp2 hzEven (by omega) hz]
    split_ifs <;> norm_num
  rw [boundaryMinusWeight, ite_eq_left hzEven]
  exact scaled_two_div_den_ne_zero 2
    (mul_ne_zero (pow_ne_zero 2 hzq) (pow_ne_zero 2 (boundaryFactor_ne_zero z))) hvden

theorem boundaryMinusWeight_odd_scaled_den_ne_zero {p z : ℕ} [hp : Fact p.Prime]
    (hzOdd : z % 2 = 1) (hz : z < p ^ 2) :
    (((p : ℚ) * boundaryMinusWeight z).den : ZMod p) ≠ 0 := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
  have hvz : padicValRat p (z : ℚ) ≤ 1 := by
    rw [padicValRat.of_nat, nat_valuation_below_prime_sq hp.out (by omega) hz]
    split_ifs <;> norm_num
  rw [boundaryMinusWeight, ite_eq_right (by omega : z % 2 ≠ 0)]
  simpa only [pow_one] using scaled_two_div_den_ne_zero 1 hzq hvz

theorem boundaryPlus_prime_sq_scaled_den_ne_zero {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryPlus (u + 1)).den : ZMod p) ≠ 0 := by
  rw [boundaryPlus_explicit]
  by_cases huEven : u % 2 = 0
  · have hH : ((boundaryFactor u).den : ZMod p) ≠ 0 := by
      apply rational_den_ne_zero_of_valuation_nonneg
      rw [boundaryFactor_even_odd_prime_valuation hp.out hp2 huEven hu]
      split_ifs <;> norm_num
    have hsum := parityBoundarySum_scaled_den_ne_zero (p := p)
      ((p : ℚ) ^ 2) boundaryPlusWeight u (by
        intro z hz0 hzu hzpar
        exact boundaryPlusWeight_even_scaled_den_ne_zero hp2 hz0
          (hzpar.trans huEven) (by omega))
    have hprod := rational_residue_mul hH hsum
    have heq : (p : ℚ) ^ 2 * (boundaryFactor u * parityBoundarySum boundaryPlusWeight u) =
        boundaryFactor u * ((p : ℚ) ^ 2 * parityBoundarySum boundaryPlusWeight u) := by ring
    rw [heq]
    exact hprod.1
  · have huOdd : u % 2 = 1 := by omega
    have hH := (boundaryFactor_odd_integral_denominators hp2 huOdd hu).2
    have hsum := parityBoundarySum_scaled_den_ne_zero (p := p)
      (p : ℚ) boundaryPlusWeight u (by
        intro z hz0 hzu hzpar
        exact boundaryPlusWeight_odd_scaled_den_ne_zero hp2
          (hzpar.trans huOdd) (by omega))
    have hprod := rational_residue_mul hH hsum
    have heq : (p : ℚ) ^ 2 * (boundaryFactor u * parityBoundarySum boundaryPlusWeight u) =
        ((p : ℚ) * boundaryFactor u) * ((p : ℚ) * parityBoundarySum boundaryPlusWeight u) := by ring
    rw [heq]
    exact hprod.1

theorem boundaryMinus_prime_sq_scaled_den_ne_zero {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) ≠ 0 := by
  rw [boundaryMinus_explicit]
  by_cases huEven : u % 2 = 0
  · have hH : ((boundaryFactor u).den : ZMod p) ≠ 0 := by
      apply rational_den_ne_zero_of_valuation_nonneg
      rw [boundaryFactor_even_odd_prime_valuation hp.out hp2 huEven hu]
      split_ifs <;> norm_num
    have hsum := parityBoundarySum_scaled_den_ne_zero (p := p)
      ((p : ℚ) ^ 2) boundaryMinusWeight u (by
        intro z hz0 hzu hzpar
        exact boundaryMinusWeight_even_scaled_den_ne_zero hp2 hz0
          (hzpar.trans huEven) (by omega))
    have hprod := rational_residue_mul hH hsum
    have heq : (p : ℚ) ^ 2 * (boundaryFactor u * parityBoundarySum boundaryMinusWeight u) =
        boundaryFactor u * ((p : ℚ) ^ 2 * parityBoundarySum boundaryMinusWeight u) := by ring
    rw [heq]
    exact hprod.1
  · have huOdd : u % 2 = 1 := by omega
    have hH := (boundaryFactor_odd_integral_denominators hp2 huOdd hu).2
    have hsum := parityBoundarySum_scaled_den_ne_zero (p := p)
      (p : ℚ) boundaryMinusWeight u (by
        intro z hz0 hzu hzpar
        exact boundaryMinusWeight_odd_scaled_den_ne_zero
          (hzpar.trans huOdd) (by omega))
    have hprod := rational_residue_mul hH hsum
    have heq : (p : ℚ) ^ 2 * (boundaryFactor u * parityBoundarySum boundaryMinusWeight u) =
        ((p : ℚ) * boundaryFactor u) * ((p : ℚ) * parityBoundarySum boundaryMinusWeight u) := by ring
    rw [heq]
    exact hprod.1

end InternalCatalan


section

open scoped BigOperators

namespace InternalCatalan

def oddHarmonicRat (u : ℕ) : ℚ :=
  ∑ z ∈ Finset.range (u + 1), if 0 < z ∧ z % 2 = 1 then 2 / (z : ℚ) else 0

@[simp] theorem oddHarmonicRat_zero : oddHarmonicRat 0 = 0 := by
  simp [oddHarmonicRat]

theorem oddHarmonicRat_succ (u : ℕ) :
    oddHarmonicRat (u + 1) = oddHarmonicRat u +
      (if 0 < u + 1 ∧ (u + 1) % 2 = 1 then 2 / ((u + 1 : ℕ) : ℚ) else 0) := by
  unfold oddHarmonicRat
  rw [Finset.sum_range_succ]

private theorem oddHarmonicTerm_den_ne_zero {p z : ℕ} [Fact p.Prime]
    (hz : ¬p ∣ z) :
    ((if 0 < z ∧ z % 2 = 1 then 2 / (z : ℚ) else 0).den : ZMod p) ≠ 0 := by
  by_cases hodd : 0 < z ∧ z % 2 = 1
  · rw [ite_eq_left hodd]
    have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hodd.1)
    have hzval : padicValRat p (z : ℚ) = 0 := by
      rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hz]
      norm_num
    apply rational_den_ne_zero_of_valuation_nonneg
    rw [padicValRat.div (by norm_num : (2 : ℚ) ≠ 0) hzq, hzval, sub_zero]
    exact zero_le_padicValRat_of_nat 2
  · simp only [ite_eq_right hodd]
    norm_num

theorem oddHarmonicRat_small_den_ne_zero {p u : ℕ} [hp : Fact p.Prime]
    (hu : u < p) : ((oddHarmonicRat u).den : ZMod p) ≠ 0 := by
  revert hu
  induction u with
  | zero => intro hu; simp
  | succ u ih =>
    intro hu
    rw [oddHarmonicRat_succ]
    exact (rational_residue_add (ih (by omega))
      (oddHarmonicTerm_den_ne_zero
        (Nat.not_dvd_of_pos_of_lt (by omega : 0 < u + 1) hu))).1

private theorem oddHarmonicTerm_scaled_zero {p z : ℕ} [Fact p.Prime]
    (hz : ¬p ∣ z) :
    (((p : ℚ) * (if 0 < z ∧ z % 2 = 1 then 2 / (z : ℚ) else 0)).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) * (if 0 < z ∧ z % 2 = 1 then 2 / (z : ℚ) else 0)).num : ZMod p) /
        (((p : ℚ) * (if 0 < z ∧ z % 2 = 1 then 2 / (z : ℚ) else 0)).den : ZMod p) = 0 := by
  have h := rational_residue_mul (a := (p : ℚ)) (by simp)
    (oddHarmonicTerm_den_ne_zero hz)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp

private theorem oddHarmonicTerm_scaled_multiple {p z : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hz : p ∣ z) :
    (p : ℚ) * (if 0 < z ∧ z % 2 = 1 then 2 / (z : ℚ) else 0) =
      (if 0 < z / p ∧ (z / p) % 2 = 1 then 2 / ((z / p : ℕ) : ℚ) else 0) := by
  have heq : z = p * (z / p) := (Nat.mul_div_cancel' hz).symm
  have hpOdd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hpar : z % 2 = (z / p) % 2 := by
    conv_lhs => rw [heq, Nat.mul_mod, hpOdd, one_mul, Nat.mod_mod]
  have hpos : 0 < z ↔ 0 < z / p := by
    constructor
    · intro hzpos
      by_contra hq
      have hq0 : z / p = 0 := Nat.eq_zero_of_not_pos hq
      rw [hq0, mul_zero] at heq
      omega
    · intro hq
      have hmul : 0 < p * (z / p) := Nat.mul_pos hp.pos hq
      rwa [← heq] at hmul
  simp only [hpos, hpar]
  by_cases hodd : 0 < z / p ∧ (z / p) % 2 = 1
  · rw [ite_eq_left hodd, ite_eq_left hodd]
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hqq : ((z / p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hodd.1)
    have hcast : (z : ℚ) = (p : ℚ) * ((z / p : ℕ) : ℚ) := by exact_mod_cast heq
    rw [hcast]
    field_simp [hpq, hqq]
  · simp only [ite_eq_right hodd, mul_zero]

theorem oddHarmonicRat_prime_digit_reduction {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p ^ 2) :
    (((p : ℚ) * oddHarmonicRat u).den : ZMod p) ≠ 0 ∧
      ((oddHarmonicRat (u / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) * oddHarmonicRat u).num : ZMod p) /
          (((p : ℚ) * oddHarmonicRat u).den : ZMod p) =
            ((oddHarmonicRat (u / p)).num : ZMod p) /
              ((oddHarmonicRat (u / p)).den : ZMod p) := by
  revert hu
  induction u with
  | zero => intro hu; simp
  | succ u ih =>
    intro hu
    have hprev := ih (by omega : u < p ^ 2)
    have hscale : (p : ℚ) * oddHarmonicRat (u + 1) =
        (p : ℚ) * oddHarmonicRat u +
          (p : ℚ) * (if 0 < u + 1 ∧ (u + 1) % 2 = 1 then
            2 / ((u + 1 : ℕ) : ℚ) else 0) := by
      rw [oddHarmonicRat_succ, mul_add]
    by_cases hdiv : p ∣ u + 1
    · have hquot : (u + 1) / p = u / p + 1 := Nat.succ_div_of_dvd hdiv
      have hsmall : u / p + 1 < p := by
        rw [← hquot]
        exact (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa only [pow_two] using hu)
      have hterm := oddHarmonicTerm_scaled_multiple hp.out hp2 hdiv
      rw [hquot] at hterm
      have htd := oddHarmonicTerm_den_ne_zero (p := p)
        (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos (u / p)) hsmall)
      have hscaledDen :
          (((p : ℚ) * (if 0 < u + 1 ∧ (u + 1) % 2 = 1 then
            2 / ((u + 1 : ℕ) : ℚ) else 0)).den : ZMod p) ≠ 0 := by
        rw [hterm]
        exact htd
      have hl := rational_residue_add hprev.1 hscaledDen
      have hr := rational_residue_add hprev.2.1 htd
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hquot, oddHarmonicRat_succ]
        exact hr.1
      · rw [hscale, hl.2, hterm, hquot, oddHarmonicRat_succ, hr.2, hprev.2.2]
    · have hquot : (u + 1) / p = u / p := Nat.succ_div_of_not_dvd hdiv
      have ht := oddHarmonicTerm_scaled_zero hdiv
      have hl := rational_residue_add hprev.1 ht.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hquot]
        exact hprev.2.1
      · rw [hscale, hl.2, ht.2, add_zero, hquot]
        exact hprev.2.2

end InternalCatalan

end


namespace InternalCatalan

theorem rational_residue_sub {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : (a.den : ZMod p) ≠ 0) (hb : (b.den : ZMod p) ≠ 0) :
    ((a - b).den : ZMod p) ≠ 0 ∧
      ((a - b).num : ZMod p) / ((a - b).den : ZMod p) =
        ((a.num : ZMod p) / (a.den : ZMod p)) -
          ((b.num : ZMod p) / (b.den : ZMod p)) := by
  have hn : ((-b).den : ZMod p) ≠ 0 := by simpa only [Rat.neg_den] using hb
  simpa only [sub_eq_add_neg, Rat.neg_num, Rat.neg_den, Int.cast_neg, neg_div] using
    rational_residue_add ha hn

end InternalCatalan


section

open scoped BigOperators

namespace InternalCatalan

theorem oddPrime_four_half_pow {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (4 : ZMod p) ^ ((p - 1) / 2) = 1 := by
  have hodd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hdeg : 2 * ((p - 1) / 2) = p - 1 := by omega
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    have hge := hp.out.two_le
    omega
  calc
    (4 : ZMod p) ^ ((p - 1) / 2) = ((2 : ZMod p) ^ 2) ^ ((p - 1) / 2) := by
      norm_num
    _ = (2 : ZMod p) ^ (2 * ((p - 1) / 2)) := (pow_mul _ _ _).symm
    _ = (2 : ZMod p) ^ (p - 1) := by rw [hdeg]
    _ = 1 := ZMod.pow_card_sub_one_eq_one htwo

theorem centralCoeff_residue_square_block {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (∑ j ∈ Finset.range ((p - 1) / 2 + 1),
      (((centralCoeff j).num : ZMod p) / ((centralCoeff j).den : ZMod p)) ^ 2) =
        (-1 : ZMod p) ^ ((p - 1) / 2) := by
  have hodd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hk : 2 * ((p - 1) / 2) < p := by omega
  have hchoose :
      (∑ j ∈ Finset.range ((p - 1) / 2 + 1),
        ((((p - 1) / 2).choose j : ℕ) : ZMod p) ^ 2) =
          ((2 * ((p - 1) / 2)).choose ((p - 1) / 2) : ZMod p) := by
    have hc := congrArg (fun n : ℕ => (n : ZMod p))
      (Nat.sum_range_choose_sq ((p - 1) / 2))
    simpa only [Nat.cast_sum, Nat.cast_pow] using hc
  calc
    _ = ∑ j ∈ Finset.range ((p - 1) / 2 + 1),
        ((((p - 1) / 2).choose j : ℕ) : ZMod p) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : 2 * j < p := by
        have hjle := Finset.mem_range.mp hj
        omega
      have hsign : ((-1 : ZMod p) ^ j) ^ 2 = 1 := by
        rw [pow_two, ← mul_pow]
        norm_num
      rw [(centralCoeff_reduced_residue hp2 j).2,
        ← oddPrimeWeight_centralCoeff_identity hp2 hjlt, mul_pow, hsign, one_mul]
    _ = ((2 * ((p - 1) / 2)).choose ((p - 1) / 2) : ZMod p) := hchoose
    _ = (-1 : ZMod p) ^ ((p - 1) / 2) := by
      simpa only [Nat.choose_self, Nat.cast_one, mul_one,
        oddPrime_four_half_pow hp2, Nat.centralBinom] using
          (oddPrimeWeight_centralCoeff_mul_identity hp.out hp2 hk).symm

theorem centralCoeff_square_block_reduction {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ((∑ j ∈ Finset.range ((p - 1) / 2 + 1), centralCoeff j ^ 2).den : ZMod p) ≠ 0 ∧
      ((∑ j ∈ Finset.range ((p - 1) / 2 + 1), centralCoeff j ^ 2).num : ZMod p) /
        ((∑ j ∈ Finset.range ((p - 1) / 2 + 1), centralCoeff j ^ 2).den : ZMod p) =
          (-1 : ZMod p) ^ ((p - 1) / 2) := by
  have hsq (j : ℕ) : ((centralCoeff j ^ 2).den : ZMod p) ≠ 0 ∧
      ((centralCoeff j ^ 2).num : ZMod p) / ((centralCoeff j ^ 2).den : ZMod p) =
        (((centralCoeff j).num : ZMod p) / ((centralCoeff j).den : ZMod p)) ^ 2 := by
    have hd := (centralCoeff_reduced_residue (p := p) hp2 j).1
    simpa only [pow_two] using rational_residue_mul hd hd
  have hs := rational_residue_sum (Finset.range ((p - 1) / 2 + 1))
    (fun j => centralCoeff j ^ 2) (fun j _ => (hsq j).1)
  refine ⟨hs.1, ?_⟩
  rw [hs.2]
  simp_rw [(hsq _).2]
  exact centralCoeff_residue_square_block hp2

end InternalCatalan

end


open scoped BigOperators

namespace InternalCatalan

theorem boundaryMinusWeight_even_no_carry_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz0 : 0 < z) (hzEven : z % 2 = 0) (hz : z < p ^ 2)
    (hr0 : z % p ≠ 0) (hrEven : (z % p) % 2 = 0) :
    (((p : ℚ) ^ 2 * boundaryMinusWeight z).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * boundaryMinusWeight z).num : ZMod p) /
        (((p : ℚ) ^ 2 * boundaryMinusWeight z).den : ZMod p) = 0 := by
  apply rational_residue_zero_of_positive_valuation
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have htwo : 0 ≤ padicValRat p (2 : ℚ) := zero_le_padicValRat_of_nat 2
  have hden : padicValRat p ((z : ℚ) ^ 2 * boundaryFactor z ^ 2) = 0 := by
    rw [← mul_pow, padicValRat.pow,
      boundaryFactor_even_mul_odd_prime_valuation hp.out hp2 hzEven (by omega) hz]
    simp [hr0, hrEven]
  rw [boundaryMinusWeight, ite_eq_left hzEven, ← mul_div_assoc,
    padicValRat.div (mul_ne_zero (pow_ne_zero 2 hpq) (by norm_num))
      (mul_ne_zero (pow_ne_zero 2 hzq) (pow_ne_zero 2 (boundaryFactor_ne_zero z))),
    padicValRat.mul (pow_ne_zero 2 hpq) (by norm_num),
    padicValRat.pow, padicValRat.self hp.out.one_lt, hden]
  omega

theorem boundaryMinus_even_scaled_residue_sum {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (huEven : u % 2 = 0) (hu : u < p ^ 2) :
    ((∑ z ∈ Finset.range (u + 1),
      if 0 < z ∧ z % 2 = 0 then (p : ℚ) ^ 2 * boundaryMinusWeight z else 0).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * boundaryMinus u).num : ZMod p) /
        (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) =
          (((boundaryFactor u).num : ZMod p) / ((boundaryFactor u).den : ZMod p)) *
            ∑ z ∈ Finset.range (u + 1),
              if 0 < z ∧ z % 2 = 0 then
                (((p : ℚ) ^ 2 * boundaryMinusWeight z).num : ZMod p) /
                  (((p : ℚ) ^ 2 * boundaryMinusWeight z).den : ZMod p)
              else 0 := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  let f : ℕ → ℚ := fun z =>
    if 0 < z ∧ z % 2 = 0 then (p : ℚ) ^ 2 * boundaryMinusWeight z else 0
  have hsum := rational_residue_sum (p := p) (Finset.range (u + 1)) f (by
    intro z hz
    dsimp only [f]
    by_cases hgood : 0 < z ∧ z % 2 = 0
    · rw [ite_eq_left hgood]
      exact boundaryMinusWeight_even_scaled_den_ne_zero hp2 hgood.1 hgood.2
        (by have := Finset.mem_range.mp hz; omega)
    · simp [hgood])
  have hH : ((boundaryFactor u).den : ZMod p) ≠ 0 := by
    apply rational_den_ne_zero_of_valuation_nonneg
    rw [boundaryFactor_even_odd_prime_valuation hp.out hp2 huEven hu]
    split_ifs <;> norm_num
  have hprod := rational_residue_mul (p := p) hH hsum.1
  have heq : (p : ℚ) ^ 2 * boundaryMinus u =
      boundaryFactor u * (∑ z ∈ Finset.range (u + 1), f z) := by
    rw [boundaryMinus_explicit, parityBoundarySum, huEven]
    simp only [f, Finset.mul_sum, mul_ite, mul_zero]
    apply Finset.sum_congr rfl
    intro z hz
    split_ifs <;> ring
  refine ⟨hsum.1, ?_⟩
  change R ((p : ℚ) ^ 2 * boundaryMinus u) = _
  rw [heq]
  calc
    _ = R (boundaryFactor u) * R (∑ z ∈ Finset.range (u + 1), f z) := hprod.2
    _ = R (boundaryFactor u) *
        (∑ z ∈ Finset.range (u + 1), R (f z)) := by
      congr 1
      exact hsum.2
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hgood : 0 < z ∧ z % 2 = 0 <;> simp [f, R, hgood]

theorem boundaryMinus_even_odd_remainder_zero {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (huEven : u % 2 = 0) (hu : u < p ^ 2)
    (hrOdd : (u % p) % 2 = 1) :
    (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * boundaryMinus u).num : ZMod p) /
        (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) = 0 := by
  refine ⟨boundaryMinus_prime_sq_scaled_den_ne_zero hp2 hu, ?_⟩
  rw [(boundaryMinus_even_scaled_residue_sum hp2 huEven hu).2,
    (boundaryFactor_even_carry_reduction hp2 huEven hu hrOdd).2, zero_mul]

end InternalCatalan

end OAI
