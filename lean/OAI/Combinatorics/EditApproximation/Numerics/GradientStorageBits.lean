import OAI.Combinatorics.EditApproximation.Numerics.RationalIntermediateBits
import OAI.Combinatorics.EditApproximation.Numerics.VectorOptimizerWork

namespace OAI

/-! Polynomial bounds for the rational data stored by the gradient and
linear-score routines, including the finite logarithm sums. -/

namespace EditApproximation

open Finset

def logarithmEncodingBudget (inputBits K : ℕ) : ℕ :=
  2 * (K * K * inputBits + K * Nat.size (2 * K + 1) + 2) + Nat.size (2 * K) + 1

theorem rationalLogApproximation_encoding_le (r : ℚ) (K B : ℕ)
    (hr : 0 ≤ r) (hbits : rationalEncodingBits r ≤ B) :
    rationalEncodingBits (rationalLogApproximation r K) ≤ logarithmEncodingBudget B K := by
  apply (rationalLogApproximation_encoding_bit_length r K hr).trans
  unfold logarithmEncodingBudget
  have h := Nat.mul_le_mul_left (K * K) hbits
  omega

def smoothedPointEncodingBudget (G B : ℕ) : ℕ := 2 * B + 100 * Nat.size G + 400

theorem smoothedPoint_encoding_le (r : ℚ) (G B : ℕ) (hbits : rationalEncodingBits r ≤ B) :
    rationalEncodingBits (r + 1 / (G : ℚ) ^ 50) ≤ smoothedPointEncodingBudget G B := by
  have hpow := rationalEncodingBits_pow (G : ℚ) 50
  rw [rationalEncodingBits_natCast] at hpow
  have hinv := rationalEncodingBits_inv ((G : ℚ) ^ 50)
  have hadd := rationalEncodingBits_add r (1 / (G : ℚ) ^ 50)
  rw [one_div] at hadd
  rw [one_div]
  unfold smoothedPointEncodingBudget
  omega

def gradientEncodingBudget (G pointBits linearBits : ℕ) : ℕ :=
  4 * logarithmEncodingBudget (smoothedPointEncodingBudget G pointBits) (G ^ 60) +
    2 * linearBits + 20

theorem rationalSmoothedGradient_encoding_le {ι : Type*} (G : ℕ)
    (linear point : ι → ℚ) (i : ι) (pointBits linearBits : ℕ)
    (hpoint : 0 ≤ point i) (hpbits : rationalEncodingBits (point i) ≤ pointBits)
    (hlbits : rationalEncodingBits (linear i) ≤ linearBits) :
    rationalEncodingBits (rationalSmoothedGradient G linear point i) ≤
      gradientEncodingBudget G pointBits linearBits := by
  have hsmooth := smoothedPoint_encoding_le (point i) G pointBits hpbits
  have hnonneg : 0 ≤ point i + 1 / (G : ℚ) ^ 50 :=
    add_nonneg hpoint (div_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _))
  have hlog := rationalLogApproximation_encoding_le _ (G ^ 60) _ hnonneg hsmooth
  have hsub := rationalEncodingBits_sub
    (-rationalLogApproximation (point i + 1 / (G : ℚ) ^ 50) (G ^ 60)) 1
  rw [rationalEncodingBits_neg] at hsub
  have hadd := rationalEncodingBits_add
    (-rationalLogApproximation (point i + 1 / (G : ℚ) ^ 50) (G ^ 60) - 1) (linear i)
  have hone : rationalEncodingBits (1 : ℚ) = 3 := by norm_num [rationalEncodingBits]
  rw [hone] at hsub
  unfold rationalSmoothedGradient gradientEncodingBudget
  omega

theorem rational_finite_sum_encoding_le {ι : Type*} (s : Finset ι) (values : ι → ℚ)
    (V B : ℕ) (habs : ∀ i ∈ s, |values i| ≤ V)
    (hbits : ∀ i ∈ s, Nat.size (values i).den ≤ B) :
    rationalEncodingBits (∑ i ∈ s, values i) ≤ Nat.size (s.card * V) + 2 * (s.card * B + 1) + 1 := by
  have hdenpos : 0 < ∏ i ∈ s, (values i).den := Finset.prod_pos (fun i _ => Rat.den_pos _)
  have hden := (Nat.size_le_size (Nat.le_of_dvd hdenpos
    (rational_finite_sum_denominator s values))).trans (natural_finite_product_bit_length s _)
  have hsum : (∑ i ∈ s, Nat.size (values i).den) ≤ s.card * B := by
    calc
      _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum hbits
      _ = _ := by simp
  have htotal : |∑ i ∈ s, values i| ≤ ((s.card * V : ℕ) : ℚ) := by
    calc
      _ ≤ ∑ i ∈ s, |values i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, (V : ℚ) := Finset.sum_le_sum habs
      _ = _ := by simp
  have hnum := (Nat.size_le_size (rational_numerator_bound _ (s.card * V) htotal)).trans
    (natural_product_bit_length _ _)
  unfold rationalEncodingBits
  omega

theorem vectorDotWithWork_encoding_le {d : ℕ} (left right : Vector ℚ d)
    (L R Bleft Bright : ℕ)
    (hleft : ∀ i, |left.get i| ≤ L)
    (hright : ∀ i, |right.get i| ≤ R)
    (hleftbits : ∀ i, Nat.size (left.get i).den ≤ Bleft)
    (hrightbits : ∀ i, Nat.size (right.get i).den ≤ Bright) :
    rationalEncodingBits (vectorDotWithWork left right).1 ≤
      Nat.size (d * (L * R)) + 2 * (d * (Bleft + Bright) + 1) + 1 := by
  rw [vectorDotWithWork_spec]
  simpa only [Prod.fst, Finset.card_univ, Fintype.card_fin] using
    (rational_finite_sum_encoding_le (Finset.univ : Finset (Fin d))
      (fun i => left.get i * right.get i) (L * R) (Bleft + Bright) (by
        intro i _
        rw [abs_mul]
        exact_mod_cast mul_le_mul (hleft i) (hright i) (abs_nonneg _) (Nat.cast_nonneg _)) (by
        intro i _
        exact (Nat.size_le_size (Nat.le_of_dvd
          (Nat.mul_pos (Rat.den_pos _) (Rat.den_pos _)) (Rat.mul_den_dvd _ _))).trans
          ((natural_product_bit_length _ _).trans
            (Nat.add_le_add (hleftbits i) (hrightbits i)))))

end EditApproximation

end OAI
