import OAI.Combinatorics.LowSpaceSubsetSum.Counting.PrimeHashCollision
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ProductHash

namespace OAI

/-!
# The at-most-three-factor nested prime construction

An increment below four contributes the factor one. Larger increments use
the actual prime range. Seed identities are retained in the product sampling
space even when numerical factors coincide. This proves the size and
collision bounds used in `alg:filter-bounds` without a coprimality premise.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

def factorRange (ell : ℕ) : Finset ℕ :=
  if ell < 4 then {1} else primeRange ell

theorem factorRange_nonempty (ell : ℕ) : (factorRange ell).Nonempty := by
  by_cases h : ell < 4
  · simp [factorRange, h]
  · simpa [factorRange, h] using primeRange_nonempty (by omega : 4 ≤ ell)

theorem factor_size_bounds {ell u p : ℕ} (hu : 1 ≤ u) (hell : ell ≤ u)
    (hp : p ∈ factorRange ell) :
    (2 : ℝ) ^ ell ≤ (32 * u : ℝ) * p ∧ (p : ℝ) ≤ (2 : ℝ) ^ ell := by
  by_cases h : ell < 4
  · have hp1 : p = 1 := by simpa [factorRange, h] using hp
    subst p
    have hpow : (2 : ℝ) ^ ell ≤ 8 := by
      have hpowN : (2 : ℕ) ^ ell ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
      exact_mod_cast hpowN
    have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
    constructor
    · norm_num only [Nat.cast_one, mul_one]
      linarith
    · simpa only [Nat.cast_one] using
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ ell)
  · have hprime : p ∈ primeRange ell := by simpa [factorRange, h] using hp
    have hlower : (2 : ℝ) ^ ell ≤ (4 * ell : ℝ) * p := by
      exact_mod_cast (Finset.mem_filter.mp hprime).2
    have huR : (ell : ℝ) ≤ u := by exact_mod_cast hell
    have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    constructor
    · nlinarith
    · exact_mod_cast (primeRange_lt (by omega : 4 ≤ ell) hprime).le

theorem factor_divisor_probability_le {ell u d : ℕ} (hu : 1 ≤ u) (hell : ell ≤ u)
    (hd : 0 < d) (hbits : d < 2 ^ (2 * u)) :
    (((factorRange ell).filter fun p => p ∣ d).card : ℝ) / (factorRange ell).card ≤
      64 * (u : ℝ) ^ 2 / (2 : ℝ) ^ ell := by
  by_cases h : ell < 4
  · have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hpow : (2 : ℝ) ^ ell ≤ 8 := by
      have hpowN : (2 : ℕ) ^ ell ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
      exact_mod_cast hpowN
    simp only [factorRange, h, ↓reduceIte, Finset.filter_singleton, one_dvd,
      ↓reduceIte, Finset.card_singleton, Nat.cast_one, div_self (by norm_num : (1 : ℝ) ≠ 0)]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ ell)).mpr
    nlinarith
  · simp only [factorRange, h, ↓reduceIte]
    apply (prime_divisor_probability_le (by omega) hell hd hbits).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg (u : ℝ)]

def tripleRange (a b c : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (factorRange a ×ˢ factorRange b) ×ˢ factorRange c

def tripleModulus (z : (ℕ × ℕ) × ℕ) : ℕ := z.1.1 * z.1.2 * z.2

theorem tripleRange_nonempty (a b c : ℕ) : (tripleRange a b c).Nonempty :=
  ((factorRange_nonempty a).product (factorRange_nonempty b)).product
    (factorRange_nonempty c)

theorem cumulative_moduli_dvd (z : (ℕ × ℕ) × ℕ) :
    z.1.1 ∣ z.1.1 * z.1.2 ∧ z.1.1 * z.1.2 ∣ tripleModulus z :=
  ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩

theorem triple_size_bounds {a b c u : ℕ} (hu : 1 ≤ u)
    (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u)
    {z : (ℕ × ℕ) × ℕ} (hz : z ∈ tripleRange a b c) :
    (2 : ℝ) ^ (a + b + c) ≤ (32 * u : ℝ) ^ 3 * tripleModulus z ∧
      (tripleModulus z : ℝ) ≤ (2 : ℝ) ^ (a + b + c) := by
  obtain ⟨hab, hcz⟩ := Finset.mem_product.mp hz
  obtain ⟨haz, hbz⟩ := Finset.mem_product.mp hab
  obtain ⟨ha0, ha1⟩ := factor_size_bounds hu ha haz
  obtain ⟨hb0, hb1⟩ := factor_size_bounds hu hb hbz
  obtain ⟨hc0, hc1⟩ := factor_size_bounds hu hc hcz
  rw [pow_add, pow_add]
  constructor
  · have hab0 := mul_le_mul ha0 hb0 (by positivity) (by positivity)
    have habc0 := mul_le_mul hab0 hc0 (by positivity) (by positivity)
    convert habc0 using 1
    simp only [tripleModulus, Nat.cast_mul]
    ring
  · have hab1 := mul_le_mul ha1 hb1 (by positivity) (by positivity)
    have habc1 := mul_le_mul hab1 hc1 (by positivity) (by positivity)
    simpa only [tripleModulus, Nat.cast_mul] using habc1

theorem triple_divisor_probability_le {a b c u d : ℕ} (hu : 1 ≤ u)
    (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u)
    (hd : 0 < d) (hbits : d < 2 ^ (2 * u)) :
    (((tripleRange a b c).filter fun z => tripleModulus z ∣ d).card : ℝ) /
      (tripleRange a b c).card ≤
        (64 * (u : ℝ) ^ 2) ^ 3 / (2 : ℝ) ^ (a + b + c) := by
  have hab := product_divisor_probability_le (factorRange a) (factorRange b)
    id id d (factorRange_nonempty a) (factorRange_nonempty b) (by positivity)
    (factor_divisor_probability_le hu ha hd hbits)
    (factor_divisor_probability_le hu hb hd hbits)
  have habc := product_divisor_probability_le (factorRange a ×ˢ factorRange b)
    (factorRange c) (fun z => z.1 * z.2) id d
    ((factorRange_nonempty a).product (factorRange_nonempty b))
    (factorRange_nonempty c) (by positivity) hab
    (factor_divisor_probability_le hu hc hd hbits)
  apply habc.trans_eq
  rw [pow_add, pow_add]
  ring

/-- The real log scale differs from the total integer increments by less than
one. All discarded increments and repeated factors are included. -/
theorem nested_size_bounds {a b c u : ℕ} {L : ℝ} (hu : 256 ≤ u)
    (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u)
    (hL0 : (a + b + c : ℕ) ≤ L) (hL1 : L < (a + b + c : ℕ) + 1)
    {z : (ℕ × ℕ) × ℕ} (hz : z ∈ tripleRange a b c) :
    (2 : ℝ) ^ L / (u : ℝ) ^ 5 ≤ tripleModulus z ∧
      (tripleModulus z : ℝ) ≤ (2 : ℝ) ^ L := by
  have huR : (256 : ℝ) ≤ u := by exact_mod_cast hu
  have hu0 : (0 : ℝ) < u := by linarith
  obtain ⟨hlower, hupper⟩ := triple_size_bounds (by omega : 1 ≤ u) ha hb hc hz
  have hpow : (2 : ℝ) ^ L ≤ 2 * (2 : ℝ) ^ (a + b + c) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hL1.le
    simpa only [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      Real.rpow_natCast, mul_comm] using h
  have hcoef : 2 * (32 * (u : ℝ)) ^ 3 ≤ (u : ℝ) ^ 5 := by
    have hu2 : (256 : ℝ) ^ 2 ≤ (u : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) huR 2
    nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ u ^ 2 - 65536)
      (pow_nonneg hu0.le 3)]
  constructor
  · apply (div_le_iff₀ (pow_pos hu0 5)).mpr
    have hscale := mul_le_mul_of_nonneg_right hcoef
      (Nat.cast_nonneg (tripleModulus z) : (0 : ℝ) ≤ tripleModulus z)
    exact hpow.trans ((mul_le_mul_of_nonneg_left hlower (by norm_num)).trans
      (by nlinarith [hscale]))
  · exact hupper.trans (by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hL0)

theorem nested_divisor_probability_le {a b c u d : ℕ} {L : ℝ} (hu : 256 ≤ u)
    (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u)
    (hL1 : L < (a + b + c : ℕ) + 1)
    (hd : 0 < d) (hbits : d < 2 ^ (2 * u)) :
    (((tripleRange a b c).filter fun z => tripleModulus z ∣ d).card : ℝ) /
      (tripleRange a b c).card ≤ (u : ℝ) ^ 10 / (2 : ℝ) ^ L := by
  have huR : (256 : ℝ) ≤ u := by exact_mod_cast hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hpow : (2 : ℝ) ^ L ≤ 2 * (2 : ℝ) ^ (a + b + c) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hL1.le
    simpa only [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      Real.rpow_natCast, mul_comm] using h
  have hcoef : 2 * (64 * (u : ℝ) ^ 2) ^ 3 ≤ (u : ℝ) ^ 10 := by
    have hu4 : (256 : ℝ) ^ 4 ≤ (u : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) huR 4
    have hprod := mul_nonneg (by nlinarith : (0 : ℝ) ≤ u ^ 4 - 524288)
      (pow_nonneg hu0.le 6)
    nlinarith
  apply (triple_divisor_probability_le (by omega : 1 ≤ u) ha hb hc hd hbits).trans
  apply (div_le_div_iff₀ (by positivity) (Real.rpow_pos_of_pos (by norm_num) L)).mpr
  have hscale := mul_le_mul_of_nonneg_right hcoef
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (a + b + c))
  exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans
    (by nlinarith [hscale])

noncomputable def tripleProbability (a b c : ℕ) (_z : (ℕ × ℕ) × ℕ) : ℝ :=
  1 / (tripleRange a b c).card

theorem tripleProbability_sum (a b c : ℕ) :
    (∑ z ∈ tripleRange a b c, tripleProbability a b c z) = 1 := by
  have h : ((tripleRange a b c).card : ℝ) ≠ 0 := by
    exact_mod_cast (tripleRange_nonempty a b c).card_pos.ne'
  simp [tripleProbability, h]

/-- The collision-energy interface is supplied for the actual product
sampler, under the same polynomial-bit difference bound as the single prime. -/
theorem nested_pairwise_collision_bound (X : Finset ℤ) {a b c u : ℕ} {L : ℝ}
    (hu : 256 ≤ u) (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u)
    (hL1 : L < (a + b + c : ℕ) + 1)
    (hbits : ∀ x ∈ X, ∀ y ∈ X, (x - y).natAbs < 2 ^ (2 * u)) :
    PairwiseCollisionBound (tripleRange a b c) (tripleProbability a b c) X
      (fun z x => x % (tripleModulus z : ℤ)) ((u : ℝ) ^ 10 / (2 : ℝ) ^ L) := by
  intro x hx y hy hxy
  have hd : 0 < (x - y).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hxy)
  have hiff (z : (ℕ × ℕ) × ℕ) :
      x % (tripleModulus z : ℤ) = y % (tripleModulus z : ℤ) ↔
        tripleModulus z ∣ (x - y).natAbs := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero,
      Int.natCast_dvd]
  have heq : (∑ z ∈ tripleRange a b c, tripleProbability a b c z *
      if x % (tripleModulus z : ℤ) = y % (tripleModulus z : ℤ) then (1 : ℝ) else 0) =
      (((tripleRange a b c).filter fun z => tripleModulus z ∣ (x - y).natAbs).card : ℝ) /
        (tripleRange a b c).card := by
    simp_rw [hiff, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    simp [tripleProbability, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact nested_divisor_probability_le hu ha hb hc hL1 hd (hbits x hx y hy)

theorem nested_occupied_probability (X : Finset ℤ) {a b c u : ℕ} {L : ℝ}
    (hu : 256 ≤ u) (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u)
    (hL1 : L < (a + b + c : ℕ) + 1)
    (hbits : ∀ x ∈ X, ∀ y ∈ X, (x - y).natAbs < 2 ^ (2 * u))
    {T : ℝ} (hT : 0 < T) :
    1 - ((X.card : ℝ) + ((u : ℝ) ^ 10 / (2 : ℝ) ^ L) * (X.card : ℝ) ^ 2) / T ≤
      ∑ z ∈ (tripleRange a b c).filter
        (fun z => (X.card : ℝ) ^ 2 / T ≤
          ((X.image (fun x => x % (tripleModulus z : ℤ))).card : ℝ)),
          tripleProbability a b c z := by
  apply occupied_probability_of_collision_bound
  · intro z _
    exact div_nonneg zero_le_one (Nat.cast_nonneg _)
  · exact tripleProbability_sum a b c
  · positivity
  · exact hT
  · exact nested_pairwise_collision_bound X hu ha hb hc hL1 hbits

end LowSpaceSubsetSum

end OAI
