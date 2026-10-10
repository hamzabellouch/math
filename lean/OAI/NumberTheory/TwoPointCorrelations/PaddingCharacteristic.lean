import OAI.NumberTheory.TwoPointCorrelations.SieveProducts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace OAI

/-! The finite characteristic product in the padding argument. The loss
from replacing `p+4` by `p` is bounded explicitly by a convergent square
sum. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def paddingCharacteristicFactor (p : ℕ) (t : ℝ) : ℝ :=
  1 - 8 * (1 - Real.cos (t * Real.log p)) / (5 * ((p : ℝ) + 4))

noncomputable def paddingCharacteristic (Q : Finset ℕ) (t : ℝ) : ℝ :=
  ∏ p ∈ Q, paddingCharacteristicFactor p t

noncomputable def paddingOscillation (Q : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ Q, (1 - Real.cos (t * Real.log p)) / p

lemma one_sub_cos_bounds (x : ℝ) : 0 ≤ 1 - Real.cos x ∧ 1 - Real.cos x ≤ 2 := by
  constructor <;> linarith [Real.cos_le_one x, Real.neg_one_le_cos x]

lemma paddingCharacteristicFactor_bounds (p : ℕ) (hp : 2 ≤ p) (t : ℝ) :
    7 / 15 ≤ paddingCharacteristicFactor p t ∧ paddingCharacteristicFactor p t ≤ 1 := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hd : 0 < 5 * ((p : ℝ) + 4) := by positivity
  have hb := one_sub_cos_bounds (t * Real.log p)
  unfold paddingCharacteristicFactor
  constructor
  · have hh : 8 * (1 - Real.cos (t * Real.log p)) / (5 * ((p : ℝ) + 4)) ≤ 8 / 15 := by
      apply (div_le_iff₀ hd).mpr
      nlinarith
    linarith
  · have hh : 0 ≤ 8 * (1 - Real.cos (t * Real.log p)) / (5 * ((p : ℝ) + 4)) :=
      div_nonneg (mul_nonneg (by norm_num) hb.1) hd.le
    linarith

lemma padding_reciprocal_shift (p : ℕ) (hp : 2 ≤ p) (u : ℝ) (hu2 : u ≤ 2) :
    u / p - u / ((p : ℝ) + 4) ≤ 8 / (p : ℝ) ^ 2 := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < (p : ℝ) ^ 2 * ((p : ℝ) + 4))).mp
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hu2 hpr.le]

theorem paddingCharacteristic_nonneg (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) (t : ℝ) :
    0 ≤ paddingCharacteristic Q t :=
  prod_nonneg (fun p hp => (by linarith [(paddingCharacteristicFactor_bounds p (hQ p hp) t).1]))

theorem paddingCharacteristic_exp_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) (t : ℝ) :
    paddingCharacteristic Q t ≤ Real.exp (64 / 5) *
      Real.exp (-(8 / 5 : ℝ) * paddingOscillation Q t) := by
  have hfirst : paddingCharacteristic Q t ≤
      Real.exp (-(8 / 5 : ℝ) * ∑ p ∈ Q, (1 - Real.cos (t * Real.log p)) / ((p : ℝ) + 4)) := by
    calc
      _ ≤ ∏ p ∈ Q, Real.exp (-(8 / 5 : ℝ) *
          ((1 - Real.cos (t * Real.log p)) / ((p : ℝ) + 4))) := by
        apply prod_le_prod₀
        · intro p hp
          linarith [(paddingCharacteristicFactor_bounds p (hQ p hp) t).1]
        · intro p hp
          have hh := Real.add_one_le_exp (-(8 / 5 : ℝ) *
            ((1 - Real.cos (t * Real.log p)) / ((p : ℝ) + 4)))
          unfold paddingCharacteristicFactor
          convert hh using 1
          field_simp
          ring
      _ = _ := by rw [← Real.exp_sum]; congr 1; rw [mul_sum]
  have hdiff : paddingOscillation Q t -
      (∑ p ∈ Q, (1 - Real.cos (t * Real.log p)) / ((p : ℝ) + 4)) ≤ 8 := by
    unfold paddingOscillation
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ Q, 8 / (p : ℝ) ^ 2 := sum_le_sum (fun p hp =>
        padding_reciprocal_shift p (hQ p hp) _
          (one_sub_cos_bounds _).2)
      _ = 8 * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ 8 := by linarith [reciprocal_square_sum_le_one Q hQ]
  apply hfirst.trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- Once the internally derived oscillatory prime estimate is supplied,
the padding Fourier decay has the exponent `6/5` required for integrability. -/
theorem paddingCharacteristic_power_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (L C t : ℝ) (hL : 0 ≤ L)
    (hprime : (3 / 4 : ℝ) * Real.log (1 + L * |t|) - C ≤ paddingOscillation Q t) :
    paddingCharacteristic Q t ≤ Real.exp ((8 / 5 : ℝ) * C + 64 / 5) *
      (1 + L * |t|) ^ (-6 / 5 : ℝ) := by
  apply (paddingCharacteristic_exp_bound Q hQ t).trans
  have hx : 0 < 1 + L * |t| := by positivity
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end TwoPointCorrelations

end OAI
