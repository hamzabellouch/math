import OAI.Combinatorics.EditApproximation.Numerics.Numerics

namespace OAI

/-!
# Concrete numerical representation and arithmetic work

These are integer bit-length and exact rational-operation bounds for the
finite optimizer. They are not a RAM theorem: the costed evaluator below
counts rational arithmetic operations, while bit-operation costs also
require the charged evaluation model used by the surrounding algorithm.
-/

namespace EditApproximation

open Finset

/-- Signed numerator plus positive denominator encoding length. -/
def rationalEncodingBits (r : ℚ) : ℕ := Nat.size r.num.natAbs + Nat.size r.den + 1

theorem natural_product_bit_length (a b : ℕ) :
    Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  calc
    a * b ≤ a * 2 ^ Nat.size b := Nat.mul_le_mul_left a (Nat.lt_size_self b).le
    _ < 2 ^ Nat.size a * 2 ^ Nat.size b :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity)
    _ = 2 ^ (Nat.size a + Nat.size b) := (pow_add _ _ _).symm

theorem natural_sum_bit_length (a b : ℕ) :
    Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ (Nat.size a + Nat.size b) :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hb : b < 2 ^ (Nat.size a + Nat.size b) :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [pow_succ]
  omega

theorem natural_power_bit_length (a n : ℕ) :
    Nat.size (a ^ n) ≤ n * Nat.size a + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hmul := natural_product_bit_length (a ^ n) a
    nlinarith

theorem natural_finite_product_bit_length {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    Nat.size (∏ i ∈ s, f i) ≤ (∑ i ∈ s, Nat.size (f i)) + 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi]
    have hmul := natural_product_bit_length (f i) (∏ j ∈ s, f j)
    omega

/-- Denominator of a finite rational sum divides the product of the
individual denominators. -/
theorem rational_finite_sum_denominator {ι : Type*} (s : Finset ι) (values : ι → ℚ) :
    (∑ i ∈ s, values i).den ∣ ∏ i ∈ s, (values i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi]
    exact (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul (dvd_refl _) ih)

/-- The symmetric logarithm parameter has a denominator bounded by
the input's numerator/denominator height. -/
theorem logarithm_parameter_denominator (r : ℚ) :
    ((r - 1) / (r + 1)).den ≤ r.num.natAbs + r.den := by
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hparameter : (r - 1) / (r + 1) =
      Rat.divInt (r.num - (r.den : ℤ)) (r.num + (r.den : ℤ)) := by
    rw [Rat.divInt_eq_div]
    push_cast
    conv_lhs => rw [← r.num_div_den]
    rw [div_sub_one hden, div_add_one hden, div_div_div_cancel_right₀ hden]
  rw [hparameter]
  by_cases hzero : r.num + (r.den : ℤ) = 0
  · simp only [hzero, Rat.divInt_zero, Rat.den_zero]
    have hpositive := r.den_pos
    omega
  · have hdivides := Rat.den_dvd (r.num - (r.den : ℤ)) (r.num + (r.den : ℤ))
    have hdividesNat : (Rat.divInt (r.num - (r.den : ℤ)) (r.num + (r.den : ℤ))).den ∣
        (r.num + (r.den : ℤ)).natAbs := by
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdivides
    exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hzero) hdividesNat).trans (by
      simpa only [Int.natAbs_natCast] using Int.natAbs_add_le r.num (r.den : ℤ))

theorem logarithm_parameter_bit_length (r : ℚ) :
    Nat.size ((r - 1) / (r + 1)).den ≤ rationalEncodingBits r := by
  exact (Nat.size_le_size (logarithm_parameter_denominator r)).trans
    (natural_sum_bit_length r.num.natAbs r.den)

def logarithmDenominatorBudget (r : ℚ) (K : ℕ) : ℕ :=
  ((r - 1) / (r + 1)).den ^ (K * K) * ∏ k ∈ range K, (2 * k + 1)

theorem sum_odd_logarithm_exponents (K : ℕ) :
    (∑ k ∈ range K, (2 * k + 1)) = K * K := by
  induction K with
  | zero => simp
  | succ K ih => rw [sum_range_succ, ih]; ring

/-- A concrete unreduced denominator for every finite logarithm sum.
The exponent `K²` is deliberately loose and keeps the proof elementary. -/
theorem rationalLogApproximation_denominator (r : ℚ) (K : ℕ) :
    (rationalLogApproximation r K).den ∣ logarithmDenominatorBudget r K := by
  let b := (r - 1) / (r + 1)
  have hterm k : (b ^ (2 * k + 1) / (2 * k + 1 : ℕ)).den ∣
      b.den ^ (2 * k + 1) * (2 * k + 1) := by
    have hmul := Rat.mul_den_dvd (b ^ (2 * k + 1)) (((2 * k + 1 : ℕ) : ℚ)⁻¹)
    rw [Rat.den_pow, Rat.inv_natCast_den_of_pos (by omega : 0 < 2 * k + 1)] at hmul
    simpa only [div_eq_mul_inv] using hmul
  have hsum := rational_finite_sum_denominator (range K)
    (fun k => b ^ (2 * k + 1) / (2 * k + 1 : ℕ))
  have hproducts := Finset.prod_dvd_prod_of_dvd (s := range K)
    (fun k => (b ^ (2 * k + 1) / (2 * k + 1 : ℕ)).den)
    (fun k => b.den ^ (2 * k + 1) * (2 * k + 1)) (fun k _ => hterm k)
  have hproduct : (∏ k ∈ range K, b.den ^ (2 * k + 1) * (2 * k + 1)) =
      logarithmDenominatorBudget r K := by
    rw [prod_mul_distrib, prod_pow_eq_pow_sum, sum_odd_logarithm_exponents]
    rfl
  have htwice := Rat.mul_den_dvd (2 : ℚ)
    (∑ k ∈ range K, b ^ (2 * k + 1) / (2 * k + 1 : ℕ))
  norm_num only [Rat.den_ofNat, one_mul] at htwice
  simpa only [rationalLogApproximation, b, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
    htwice.trans (hsum.trans (hproduct ▸ hproducts))

theorem logarithmDenominatorBudget_positive (r : ℚ) (K : ℕ) :
    0 < logarithmDenominatorBudget r K := by
  unfold logarithmDenominatorBudget
  exact Nat.mul_pos (pow_pos (Rat.den_pos _) _) (prod_pos (fun k _ => by omega))

/-- Polynomial bit length of the actual logarithm denominator in the
input encoding length and truncation count. -/
theorem rationalLogApproximation_denominator_bit_length (r : ℚ) (K : ℕ) :
    Nat.size (rationalLogApproximation r K).den ≤
      K * K * rationalEncodingBits r + K * Nat.size (2 * K + 1) + 2 := by
  have hden := Nat.le_of_dvd (logarithmDenominatorBudget_positive r K)
    (rationalLogApproximation_denominator r K)
  have hmono := Nat.size_le_size hden
  have hmul := natural_product_bit_length (((r - 1) / (r + 1)).den ^ (K * K))
    (∏ k ∈ range K, (2 * k + 1))
  have hpower := natural_power_bit_length ((r - 1) / (r + 1)).den (K * K)
  have hproduct := natural_finite_product_bit_length (range K) (fun k => 2 * k + 1)
  have hsum : (∑ k ∈ range K, Nat.size (2 * k + 1)) ≤ K * Nat.size (2 * K + 1) := by
    calc
      _ ≤ ∑ _ ∈ range K, Nat.size (2 * K + 1) := sum_le_sum (fun k hk =>
        Nat.size_le_size (by have hkK := mem_range.mp hk; omega))
      _ = _ := by simp
  have hinput := Nat.mul_le_mul_left (K * K) (logarithm_parameter_bit_length r)
  dsimp only [logarithmDenominatorBudget] at hmono
  omega

/-- Costed repeated multiplication, counting one rational
multiplication at each successor. -/
def rationalPowerWithWork (r : ℚ) : ℕ → ℚ × ℕ
  | 0 => (1, 0)
  | n + 1 => let previous := rationalPowerWithWork r n
    (previous.1 * r, previous.2 + 1)

theorem rationalPowerWithWork_spec (r : ℚ) (n : ℕ) :
    rationalPowerWithWork r n = (r ^ n, n) := by
  induction n with
  | zero => simp [rationalPowerWithWork]
  | succ n ih => simp [rationalPowerWithWork, ih, pow_succ]

/-- The direct finite logarithm summation, with every power,
division and addition counted. -/
def rationalLogPartialWithWork (b : ℚ) : ℕ → ℚ × ℕ
  | 0 => (0, 0)
  | K + 1 =>
    let previous := rationalLogPartialWithWork b K
    let power := rationalPowerWithWork b (2 * K + 1)
    (previous.1 + power.1 / (2 * K + 1 : ℕ), previous.2 + power.2 + 2)

theorem rationalLogPartialWithWork_spec (b : ℚ) (K : ℕ) :
    rationalLogPartialWithWork b K =
      (∑ k ∈ range K, b ^ (2 * k + 1) / (2 * k + 1 : ℕ), K * K + 2 * K) := by
  induction K with
  | zero => simp [rationalLogPartialWithWork]
  | succ K ih =>
    simp only [rationalLogPartialWithWork, ih, rationalPowerWithWork_spec, sum_range_succ]
    congr 1
    ring

/-- Three operations form the logarithm parameter, and one final
multiplication doubles the partial sum. -/
def rationalLogApproximationWithWork (r : ℚ) (K : ℕ) : ℚ × ℕ :=
  let seriesResult := rationalLogPartialWithWork ((r - 1) / (r + 1)) K
  (2 * seriesResult.1, seriesResult.2 + 4)

/-- The actual logarithm evaluator uses exactly a quadratic number of
rational arithmetic operations and returns the already verified value. -/
theorem rationalLogApproximationWithWork_spec (r : ℚ) (K : ℕ) :
    rationalLogApproximationWithWork r K =
      (rationalLogApproximation r K, K * K + 2 * K + 4) := by
  simp [rationalLogApproximationWithWork, rationalLogPartialWithWork_spec, rationalLogApproximation]

/-- Every logarithm series term is bounded on nonnegative inputs;
this controls the returned numerator without transcendental arithmetic. -/
theorem rationalLogApproximation_abs_bound (r : ℚ) (K : ℕ) (hr : 0 ≤ r) :
    |rationalLogApproximation r K| ≤ 2 * K := by
  let b := (r - 1) / (r + 1)
  have hrden : 0 < r + 1 := by linarith
  have hb : |b| ≤ 1 := by
    dsimp only [b]
    rw [abs_div, abs_of_pos hrden]
    apply (div_le_one₀ hrden).mpr
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hterm (k : ℕ) : |b ^ (2 * k + 1) / (2 * k + 1 : ℕ)| ≤ 1 := by
    have hden : (1 : ℚ) ≤ (2 * k + 1 : ℕ) := by norm_cast; omega
    have hdenpos : (0 : ℚ) < (2 * k + 1 : ℕ) := by positivity
    rw [abs_div, abs_pow, abs_of_pos hdenpos]
    calc
      _ ≤ (1 : ℚ) / (2 * k + 1 : ℕ) := div_le_div_of_nonneg_right
        (pow_le_one₀ (abs_nonneg b) hb) hdenpos.le
      _ ≤ 1 := (div_le_one₀ hdenpos).mpr hden
  have hsum : |∑ k ∈ range K, b ^ (2 * k + 1) / (2 * k + 1 : ℕ)| ≤ K := by
    calc
      _ ≤ ∑ k ∈ range K, |b ^ (2 * k + 1) / (2 * k + 1 : ℕ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ range K, (1 : ℚ) := sum_le_sum (fun k _ => hterm k)
      _ = K := by simp
  unfold rationalLogApproximation
  push_cast at hsum
  dsimp only [b] at hsum
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2)]
  linarith

theorem rational_numerator_bound (r : ℚ) (M : ℕ) (hM : |r| ≤ M) :
    r.num.natAbs ≤ M * r.den := by
  have hscaled := mul_le_mul_of_nonneg_right hM (show (0 : ℚ) ≤ r.den by positivity)
  have hnum : |r| * (r.den : ℚ) = (r.num.natAbs : ℚ) := by
    calc
      _ = |r * (r.den : ℚ)| := by rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ r.den)]
      _ = |(r.num : ℚ)| := by rw [Rat.mul_den_eq_num]
      _ = (r.num.natAbs : ℚ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hnum] at hscaled
  exact_mod_cast hscaled

/-- Polynomial bit-length bound for both numerator and denominator of
all actually returned logarithm approximations. -/
theorem rationalLogApproximation_encoding_bit_length (r : ℚ) (K : ℕ) (hr : 0 ≤ r) :
    rationalEncodingBits (rationalLogApproximation r K) ≤
      2 * (K * K * rationalEncodingBits r + K * Nat.size (2 * K + 1) + 2) +
        Nat.size (2 * K) + 1 := by
  have habsolute := rationalLogApproximation_abs_bound r K hr
  have habsolute' : |rationalLogApproximation r K| ≤ ((2 * K : ℕ) : ℚ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using habsolute
  have hnum := Nat.size_le_size (rational_numerator_bound _ (2 * K) habsolute')
  have hmul := natural_product_bit_length (2 * K) (rationalLogApproximation r K).den
  have hden := rationalLogApproximation_denominator_bit_length r K
  dsimp only [rationalEncodingBits] at hden ⊢
  omega

/-- Stored mixture coefficients use a denominator dividing `K(K+1)`;
there is no growth with the number of earlier optimizer updates. -/
theorem optimizerMixtureWeight_denominator (K j : ℕ) (hK : 0 < K) :
    (optimizerMixtureWeight K j).den ∣ K * (K + 1) := by
  have hrepresentation : optimizerMixtureWeight K j =
      ((2 * (j + 1) : ℕ) : ℚ) * (((K * (K + 1) : ℕ) : ℚ))⁻¹ := by
    unfold optimizerMixtureWeight
    push_cast
    ring
  rw [hrepresentation]
  have hpositive : 0 < K * (K + 1) := Nat.mul_pos hK (by omega)
  simpa only [Rat.den_natCast, Rat.inv_natCast_den_of_pos hpositive, one_mul] using
    Rat.mul_den_dvd (((2 * (j + 1) : ℕ) : ℚ)) (((K * (K + 1) : ℕ) : ℚ))⁻¹

theorem optimizerMixtureWeight_bit_length (K j : ℕ) (hK : 0 < K) :
    Nat.size (optimizerMixtureWeight K j).den ≤ 2 * Nat.size K + 2 := by
  have hpositive : 0 < K * (K + 1) := Nat.mul_pos hK (by omega)
  have hden := Nat.size_le_size (Nat.le_of_dvd hpositive (optimizerMixtureWeight_denominator K j hK))
  have hmul := natural_product_bit_length K (K + 1)
  have hadd := natural_sum_bit_length K 1
  norm_num only [Nat.size_one] at hadd
  omega

/-- Every actual rational iterate has a polynomial denominator bit
length in its trace length and the listed vertices' input bit bound. -/
theorem rationalOptimizerIterate_denominator_bit_length {ι : Type*}
    (initial : ι → ℚ) (selected : ℕ → ι → ℚ) (K B : ℕ) (hK : 0 < K) (i : ι)
    (hinput : ∀ j ∈ range K, Nat.size (selected j i).den ≤ B) :
    Nat.size (rationalOptimizerIterate initial selected K i).den ≤
      K * (2 * Nat.size K + 2 + B) + 1 := by
  have hmixture := rationalOptimizerIterate_eq_mixture initial selected (K - 1) i
  rw [Nat.sub_add_cancel (show 1 ≤ K by omega)] at hmixture
  rw [hmixture]
  have hdivides := rational_finite_sum_denominator (range K)
    (fun j => optimizerMixtureWeight K j * selected j i)
  have hpositive : 0 < ∏ j ∈ range K, (optimizerMixtureWeight K j * selected j i).den :=
    prod_pos (fun _ _ => Rat.den_pos _)
  have hden := Nat.size_le_size (Nat.le_of_dvd hpositive hdivides)
  have hproduct := natural_finite_product_bit_length (range K)
    (fun j => (optimizerMixtureWeight K j * selected j i).den)
  have hterm j (hj : j ∈ range K) : Nat.size (optimizerMixtureWeight K j * selected j i).den ≤
      2 * Nat.size K + 2 + B := by
    have hmulden := Nat.size_le_size (Nat.le_of_dvd
      (Nat.mul_pos (Rat.den_pos (optimizerMixtureWeight K j)) (Rat.den_pos (selected j i)))
      (Rat.mul_den_dvd (optimizerMixtureWeight K j) (selected j i)))
    have hmul := natural_product_bit_length (optimizerMixtureWeight K j).den (selected j i).den
    have hweight := optimizerMixtureWeight_bit_length K j hK
    have hselected := hinput j hj
    omega
  have hsum : (∑ j ∈ range K, Nat.size (optimizerMixtureWeight K j * selected j i).den) ≤
      K * (2 * Nat.size K + 2 + B) := by
    calc
      _ ≤ ∑ _ ∈ range K, (2 * Nat.size K + 2 + B) := sum_le_sum hterm
      _ = _ := by simp
  omega

end EditApproximation

end OAI
