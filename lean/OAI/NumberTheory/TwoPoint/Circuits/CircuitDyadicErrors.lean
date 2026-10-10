import OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicBudgets

namespace OAI

/-! The two losses in Braverman's comparison fit a common dyadic error
budget. These are scalar inequalities, independent of the circuit. -/

namespace TwoPointCorrelations

lemma dyadic_cancel (a b : ℕ) :
    (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (a + b) = (1 / 2 : ℝ) ^ b := by
  rw [pow_add]
  calc
    _ = (2 * (1 / 2) : ℝ) ^ a * (1 / 2 : ℝ) ^ b := by rw [mul_pow]; ring
    _ = _ := by norm_num

lemma braverman_exception_loss (j : ℕ) :
    8 * ((2 : ℝ) ^ j * (7 / 8 : ℝ) ^ bravermanSamples j) ≤
      (1 / 2 : ℝ) ^ (j + 1) := by
  have hsmall : (7 / 8 : ℝ) ^ bravermanSamples j ≤ (1 / 2 : ℝ) ^ (2 * j + 4) := by
    calc
      _ = ((7 / 8 : ℝ) ^ 40) ^ (j + 1) := by rw [← pow_mul]; rfl
      _ ≤ ((1 / 2 : ℝ) ^ 5) ^ (j + 1) :=
        pow_le_pow_left₀ (by positivity) (by norm_num) _
      _ = (1 / 2 : ℝ) ^ (5 * (j + 1)) := by rw [pow_mul]
      _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc
    _ ≤ 8 * ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (2 * j + 4)) := by gcongr
    _ = (2 : ℝ) ^ (j + 3) * (1 / 2 : ℝ) ^ ((j + 3) + (j + 1)) := by
      have hcoef : 8 * (2 : ℝ) ^ j = (2 : ℝ) ^ (j + 3) := by rw [pow_add]; ring
      rw [← mul_assoc, hcoef]
      congr 2
      omega
    _ = _ := dyadic_cancel _ _

lemma braverman_spectral_loss (j : ℕ) :
    2 * ((2 : ℝ) ^ bravermanNormExponent j) ^ 2 *
      (4 * (2 : ℝ) ^ bravermanErrorExponent j *
        (1 / 2 : ℝ) ^ (bravermanSwitches j + 1)) ≤
      (1 / 2 : ℝ) ^ (j + 1) := by
  let a := 2 * bravermanNormExponent j + bravermanErrorExponent j + 3
  have he : bravermanSwitches j + 1 = a + (j + 8) := by
    dsimp [bravermanSwitches, a]
    omega
  have hcoef : 2 * ((2 : ℝ) ^ bravermanNormExponent j) ^ 2 *
      (4 * (2 : ℝ) ^ bravermanErrorExponent j) = (2 : ℝ) ^ a := by
    dsimp [a]
    rw [pow_add, pow_add, show 2 * bravermanNormExponent j =
      bravermanNormExponent j * 2 by omega, pow_mul]
    ring
  calc
    _ = (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (a + (j + 8)) := by
      rw [he]
      rw [← mul_assoc, hcoef]
    _ = (1 / 2 : ℝ) ^ (j + 8) := dyadic_cancel _ _
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

lemma braverman_total_loss (j : ℕ) :
    8 * ((2 : ℝ) ^ j * (7 / 8 : ℝ) ^ bravermanSamples j) +
      2 * ((2 : ℝ) ^ bravermanNormExponent j) ^ 2 *
        (4 * (2 : ℝ) ^ bravermanErrorExponent j *
          (1 / 2 : ℝ) ^ (bravermanSwitches j + 1)) ≤ (1 / 2 : ℝ) ^ j := by
  have h₁ := braverman_exception_loss j
  have h₂ := braverman_spectral_loss j
  have he : (1 / 2 : ℝ) ^ (j + 1) + (1 / 2 : ℝ) ^ (j + 1) =
      (1 / 2 : ℝ) ^ j := by rw [pow_succ]; ring
  exact (add_le_add h₁ h₂).trans_eq he

end TwoPointCorrelations

end OAI
