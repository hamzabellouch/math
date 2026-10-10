import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationChosenStreams
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FixedBuckets

namespace OAI

/-! # The concrete extra-prime parameter and its hashing bounds -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

open scoped BigOperators

variable {n : ℕ} (R : RepresentationSetup n)

theorem filterDeficit_mono (z : Layout n) : Monotone (R.filterDeficit z) := by
  intro i j hij
  have h := R.lowExponent_antitone z hij
  rw [R.lowExponent_eq_half_sub, R.lowExponent_eq_half_sub] at h
  linarith

theorem filterDeficit_nonneg (z : Layout n) (i : Fin 3) : 0 ≤ R.filterDeficit z i :=
  le_min (by positivity) (div_nonneg (deficiency_nonneg _ _) (by norm_num))

/-- This is the manuscript's maximum over the three ordered mixers. -/
def extraPrimeRate (z : Layout n) : ℝ :=
  extraPrimeExponent n (mixerSize n) (R.filterDeficit z 2)

theorem extraPrimeRate_max (z : Layout n) :
    R.extraPrimeRate z = extraPrimeExponent n (mixerSize n)
      (max (R.filterDeficit z 0) (max (R.filterDeficit z 1) (R.filterDeficit z 2))) := by
  rw [max_eq_right (R.filterDeficit_mono z (by decide : (1 : Fin 3) ≤ 2)),
    max_eq_right (R.filterDeficit_mono z (by decide : (0 : Fin 3) ≤ 2))]
  rfl

/-- The actual integer sampling parameter, including both floors. -/
def extraPrimeParameter (z : Layout n) : ℕ :=
  ⌊(n : ℝ) / 4 + (4 / 125 : ℝ) * mixerSize n - (mixerSize n : ℝ) / 2 +
    (min ⌊R.lowExponent z 0⌋₊ (min ⌊R.lowExponent z 1⌋₊ ⌊R.lowExponent z 2⌋₊) : ℕ)⌋₊

theorem extraPrimeParameter_eq (z : Layout n) :
    R.extraPrimeParameter z =
      ⌊(n : ℝ) / 4 + (4 / 125 : ℝ) * mixerSize n - (mixerSize n : ℝ) / 2 +
        (⌊R.lowExponent z 2⌋₊ : ℝ)⌋₊ := by
  have h12 := Nat.floor_mono (R.lowExponent_antitone z (by decide : (1 : Fin 3) ≤ 2))
  have h02 := Nat.floor_mono (R.lowExponent_antitone z (by decide : (0 : Fin 3) ≤ 2))
  simp only [extraPrimeParameter, min_eq_right h12, min_eq_right h02]

theorem extraPrimeRate_bounds (z : Layout n) :
    (1211 / 5000 : ℝ) * n ≤ R.extraPrimeRate z ∧
      R.extraPrimeRate z ≤ (3221 / 12500 : ℝ) * n := by
  have hf := R.filterDeficit_le_tau z 2
  have hf0 := R.filterDeficit_nonneg z 2
  have hm0 : (0 : ℝ) ≤ mixerSize n := Nat.cast_nonneg _
  have hm := (mixerSize_bounds n).2
  dsimp only [extraPrimeRate, extraPrimeExponent]
  constructor <;> linarith

theorem extraPrimeParameter_bounds (z : Layout n) (hn : 100 ≤ n) :
    R.extraPrimeRate z - 2 < (R.extraPrimeParameter z : ℝ) ∧
      (R.extraPrimeParameter z : ℝ) ≤ R.extraPrimeRate z := by
  rw [R.extraPrimeParameter_eq]
  have hl := Nat.lt_floor_add_one (R.lowExponent z 2)
  have hu := Nat.floor_le (R.lowExponent_nonneg z 2)
  have he := R.lowExponent_eq_half_sub z 2
  have hx := (R.extraPrimeRate_bounds z).1
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  let y := (n : ℝ) / 4 + (4 / 125 : ℝ) * mixerSize n - (mixerSize n : ℝ) / 2 +
    (⌊R.lowExponent z 2⌋₊ : ℝ)
  have hylo : R.extraPrimeRate z - 1 < y := by
    dsimp only [extraPrimeRate, extraPrimeExponent, y] at *
    linarith
  have hyhi : y ≤ R.extraPrimeRate z := by
    dsimp only [extraPrimeRate, extraPrimeExponent, y] at *
    linarith
  have hy0 : 0 ≤ y := by linarith
  have hyl := Nat.lt_floor_add_one y
  have hyu := Nat.floor_le hy0
  change R.extraPrimeRate z - 2 < (⌊y⌋₊ : ℝ) ∧ (⌊y⌋₊ : ℝ) ≤ R.extraPrimeRate z
  constructor <;> linarith

theorem extraPrimeParameter_range (z : Layout n) (hn : 100 ≤ n) :
    4 ≤ R.extraPrimeParameter z ∧ R.extraPrimeParameter z ≤ n := by
  have h := R.extraPrimeParameter_bounds z hn
  have hx := R.extraPrimeRate_bounds z
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · have hl : (4 : ℝ) ≤ R.extraPrimeParameter z := by linarith
    exact_mod_cast hl
  · have hu : (R.extraPrimeParameter z : ℝ) ≤ n := by linarith
    exact_mod_cast hu

/-- Rejection sampling in the full bit range has inverse-polynomial density. -/
theorem extraPrime_density (z : Layout n) (hn : 100 ≤ n) :
    1 / (4 * (n : ℝ)) ≤
      ((primeRange (R.extraPrimeParameter z)).card : ℝ) /
        (2 : ℝ) ^ R.extraPrimeParameter z := by
  have hr := R.extraPrimeParameter_range z hn
  have hc : (2 : ℝ) ^ R.extraPrimeParameter z ≤
      4 * R.extraPrimeParameter z * (primeRange (R.extraPrimeParameter z)).card := by
    exact_mod_cast primeRange_card_lower hr.1
  have he : (R.extraPrimeParameter z : ℝ) ≤ n := by exact_mod_cast hr.2
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_right he
    (show 0 ≤ (primeRange (R.extraPrimeParameter z)).card * (4 : ℝ) by positivity)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith


/-- Every sampled extra prime has the manuscript's actual size bounds. -/
theorem extraPrime_size (z : Layout n) (hn : 100 ≤ n) {q : ℕ}
    (hq : q ∈ primeRange (R.extraPrimeParameter z)) :
    (2 : ℝ) ^ R.extraPrimeRate z / (inputScale R.input : ℝ) ^ 2 ≤ q ∧
      (q : ℝ) ≤ (2 : ℝ) ^ R.extraPrimeRate z := by
  have hr := R.extraPrimeParameter_range z hn
  have hf := R.extraPrimeParameter_bounds z hn
  have hu : (100 : ℝ) ≤ inputScale R.input := by
    exact_mod_cast (show 100 ≤ inputScale R.input by unfold inputScale; omega)
  have hellu : (R.extraPrimeParameter z : ℝ) ≤ inputScale R.input := by
    exact_mod_cast (show R.extraPrimeParameter z ≤ inputScale R.input by
      exact hr.2.trans (by unfold inputScale; omega))
  have hqlo : (2 : ℝ) ^ R.extraPrimeParameter z ≤
      4 * R.extraPrimeParameter z * (q : ℝ) := by
    exact_mod_cast (Finset.mem_filter.mp hq).2
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hp : (2 : ℝ) ^ R.extraPrimeRate z ≤
      4 * (2 : ℝ) ^ R.extraPrimeParameter z := by
    calc
      _ ≤ (2 : ℝ) ^ ((R.extraPrimeParameter z : ℝ) + 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := by rw [Real.rpow_add (by norm_num), Real.rpow_natCast]; norm_num; ring
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < (inputScale R.input : ℝ) ^ 2)).mpr
    have hku := mul_le_mul_of_nonneg_right hellu hq0
    have hu2 : 16 * (inputScale R.input : ℝ) ≤ (inputScale R.input : ℝ) ^ 2 := by nlinarith
    have huu := mul_le_mul_of_nonneg_right hu2 hq0
    nlinarith
  · have hqhi : (q : ℝ) ≤ (2 : ℝ) ^ R.extraPrimeParameter z := by
      exact_mod_cast (primeRange_lt hr.1 hq).le
    apply hqhi.trans
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hf.2

/-- Prime hashing bound with the paper's simplified cubic input-scale factor. -/
theorem extraPrime_collision (z : Layout n) (hn : 100 ≤ n) (X : Finset ℤ)
    (hbits : ∀ x ∈ X, ∀ y ∈ X, (x - y).natAbs < 2 ^ (2 * inputScale R.input)) :
    PairwiseCollisionBound (primeRange (R.extraPrimeParameter z))
      (primeProbability (R.extraPrimeParameter z)) X
      (fun q x => x % (q : ℤ))
      ((inputScale R.input : ℝ) ^ 3 / (2 : ℝ) ^ R.extraPrimeRate z) := by
  have hr := R.extraPrimeParameter_range z hn
  have hellu : R.extraPrimeParameter z ≤ inputScale R.input :=
    hr.2.trans (by unfold inputScale; omega)
  have hcol := prime_pairwise_collision_bound X hr.1 hellu hbits
  have hu : (100 : ℝ) ≤ inputScale R.input := by
    exact_mod_cast (show 100 ≤ inputScale R.input by unfold inputScale; omega)
  have hpow : (2 : ℝ) ^ R.extraPrimeRate z ≤
      4 * (2 : ℝ) ^ R.extraPrimeParameter z := by
    calc
      _ ≤ (2 : ℝ) ^ ((R.extraPrimeParameter z : ℝ) + 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by linarith [(R.extraPrimeParameter_bounds z hn).1])
      _ = _ := by rw [Real.rpow_add (by norm_num), Real.rpow_natCast]; norm_num; ring
  have hdelta : 8 * (inputScale R.input : ℝ) ^ 2 /
      (2 : ℝ) ^ R.extraPrimeParameter z ≤
      (inputScale R.input : ℝ) ^ 3 / (2 : ℝ) ^ R.extraPrimeRate z := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hu3 : 32 * (inputScale R.input : ℝ) ^ 2 ≤ (inputScale R.input : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (show 0 ≤ (inputScale R.input : ℝ) - 32 by linarith)
        (sq_nonneg (inputScale R.input : ℝ))]
    have he3 := mul_le_mul_of_nonneg_right hu3
      (show 0 ≤ (2 : ℝ) ^ R.extraPrimeParameter z by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ 8 * (inputScale R.input : ℝ) ^ 2 by positivity)]
  intro x hx y hy hxy
  exact (hcol x hx y hy hxy).trans hdelta

/-- Using the full parent modulus adds no coprimality assumption: a collision
modulo its product with `q` is in particular a collision modulo `q`. -/
theorem extraPrime_product_collision (z : Layout n) (hn : 100 ≤ n)
    (p0 : ℕ) (X : Finset ℤ)
    (hbits : ∀ x ∈ X, ∀ y ∈ X, (x - y).natAbs < 2 ^ (2 * inputScale R.input)) :
    PairwiseCollisionBound (primeRange (R.extraPrimeParameter z))
      (primeProbability (R.extraPrimeParameter z)) X
      (fun q x => x % ((p0 : ℤ) * q))
      ((inputScale R.input : ℝ) ^ 3 / (2 : ℝ) ^ R.extraPrimeRate z) := by
  have hc := R.extraPrime_collision z hn X hbits
  intro x hx y hy hxy
  apply le_trans _ (hc x hx y hy hxy)
  apply Finset.sum_le_sum
  intro q _
  have hprob : 0 ≤ primeProbability (R.extraPrimeParameter z) q := by
    unfold primeProbability
    positivity
  by_cases hp : x % ((p0 : ℤ) * q) = y % ((p0 : ℤ) * q)
  · have hq : x % (q : ℤ) = y % (q : ℤ) :=
      (show Int.ModEq ((p0 : ℤ) * q) x y from hp).of_dvd
        (show (q : ℤ) ∣ (p0 : ℤ) * q from ⟨p0, by ring⟩)
    simp only [hp, hq, ↓reduceIte, le_refl]
  · simp only [hp, ↓reduceIte, mul_zero]
    split_ifs <;> positivity


end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
