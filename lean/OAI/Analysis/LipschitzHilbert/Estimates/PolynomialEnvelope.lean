import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialLocalization
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! Polynomial growth about a box is absorbed by a slower packet envelope.
The integrated envelope has the packet length as its only scale factor. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

def lineEnvelope (a l : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((1 + ((x - a) / l) ^ 2) ^ n)⁻¹

theorem lineEnvelope_nonneg (a l : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ lineEnvelope a l n x := by
  unfold lineEnvelope
  positivity

theorem polynomial_base_le (x s a l r : ℝ) (hl : 0 < l) (hr : 0 < r)
    (hlr : l ≤ r) (hsa : |s - a| ≤ r) :
    1 + (x - a) ^ 2 / r ^ 2 ≤ 4 * (1 + ((x - s) / l) ^ 2) := by
  have hu : |(x - s) / r| ≤ |(x - s) / l| := by
    rw [abs_div, abs_div, abs_of_pos hr, abs_of_pos hl]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hl hlr
  have hv : |(s - a) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact hsa
  have hu2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hu
  have hv2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr hv
  simp only [sq_abs, one_pow] at hu2 hv2
  have heq : (x - a) / r = (x - s) / r + (s - a) / r := by ring
  rw [← div_pow, heq]
  nlinarith [sq_nonneg ((x - s) / r - (s - a) / r), sq_nonneg ((x - s) / l)]

theorem polynomialWeight_sq_mul_envelope (x s a l r : ℝ) (q n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hsa : |s - a| ≤ r) :
    polynomialWeight a r q x ^ 2 * lineEnvelope s l (n + 2 * q) x ≤
      16 ^ q * lineEnvelope s l n x := by
  let B := 1 + ((x - s) / l) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hbase := polynomial_base_le x s a l r hl hr hlr hsa
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + (x - a) ^ 2 / r ^ 2)
    hbase (2 * q)
  have hweight : polynomialWeight a r q x ^ 2 = (1 + (x - a) ^ 2 / r ^ 2) ^ (2 * q) := by
    simp only [polynomialWeight, ← pow_mul, Nat.mul_comm q 2]
  rw [hweight]
  calc
    _ ≤ (4 * B) ^ (2 * q) * (B ^ (n + 2 * q))⁻¹ :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 16 ^ q * lineEnvelope s l n x := by
      change (4 * B) ^ (2 * q) * (B ^ (n + 2 * q))⁻¹ = 16 ^ q * (B ^ n)⁻¹
      rw [mul_pow, pow_add, mul_inv_rev, ← mul_assoc]
      have hz : B ^ (2 * q) ≠ 0 := pow_ne_zero _ hB.ne'
      have hc : (4 : ℝ) ^ (2 * q) = 16 ^ q := by rw [pow_mul]; norm_num
      rw [mul_assoc ((4 : ℝ) ^ (2 * q)), mul_inv_cancel₀ hz, mul_one, hc]

theorem integral_lineEnvelope_one (a l : ℝ) (hl : 0 < l) :
    (∫ x, lineEnvelope a l 1 x) = Real.pi * l := by
  simp only [lineEnvelope, pow_one]
  rw [integral_sub_right_eq_self (fun x : ℝ => (1 + (x / l) ^ 2)⁻¹),
    Measure.integral_comp_div (fun y : ℝ => (1 + y ^ 2)⁻¹) l,
    integral_univ_inv_one_add_sq, abs_of_pos hl]
  ring

theorem integrable_lineEnvelope_one (a l : ℝ) (hl : 0 < l) :
    Integrable (lineEnvelope a l 1) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_lineEnvelope_one a l hl]
  exact mul_ne_zero Real.pi_ne_zero hl.ne'

theorem lineEnvelope_antitone (a l x : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    lineEnvelope a l n x ≤ lineEnvelope a l m x := by
  have hb : 1 ≤ 1 + ((x - a) / l) ^ 2 := by nlinarith [sq_nonneg ((x - a) / l)]
  unfold lineEnvelope
  exact inv_anti₀ (pow_pos (by positivity) m) (pow_le_pow_right₀ hb hmn)

theorem integrable_lineEnvelope (a l : ℝ) (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (lineEnvelope a l n) := by
  have hm : Measurable (lineEnvelope a l n) := by unfold lineEnvelope; fun_prop
  apply (integrable_lineEnvelope_one a l hl).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (lineEnvelope_nonneg a l n x)]
  exact lineEnvelope_antitone a l x hn

theorem integral_lineEnvelope_le (a l : ℝ) (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n) :
    (∫ x, lineEnvelope a l n x) ≤ Real.pi * l := by
  rw [← integral_lineEnvelope_one a l hl]
  exact integral_mono (integrable_lineEnvelope a l hl hn)
    (integrable_lineEnvelope_one a l hl) (fun x => lineEnvelope_antitone a l x hn)

theorem polynomialLocalization_energy (f : SchwartzMap ℝ ℂ) (s a l r A : ℝ) (q : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hsa : |s - a| ≤ r) (hA : 0 ≤ A)
    (henv : ∀ x, ‖f x‖ ^ 2 ≤ A * lineEnvelope s l (1 + 2 * q) x) :
    (∫ x, ‖polynomialLocalization a r q f x‖ ^ 2) ≤ 16 ^ q * A * (Real.pi * l) := by
  have hpoint (x : ℝ) : ‖polynomialLocalization a r q f x‖ ^ 2 ≤
      (16 ^ q * A) * lineEnvelope s l 1 x := by
    have hnorm : ‖polynomialLocalization a r q f x‖ ^ 2 =
        polynomialWeight a r q x ^ 2 * ‖f x‖ ^ 2 := by
      rw [polynomialLocalization_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ((polynomialWeight_one_le a r q x).trans' (by norm_num)), mul_pow]
    rw [hnorm]
    calc
      _ ≤ polynomialWeight a r q x ^ 2 * (A * lineEnvelope s l (1 + 2 * q) x) :=
        mul_le_mul_of_nonneg_left (henv x) (sq_nonneg _)
      _ = A * (polynomialWeight a r q x ^ 2 * lineEnvelope s l (1 + 2 * q) x) := by ring
      _ ≤ A * (16 ^ q * lineEnvelope s l 1 x) :=
        mul_le_mul_of_nonneg_left (polynomialWeight_sq_mul_envelope x s a l r q 1
          hl hr hlr hsa) hA
      _ = _ := by ring
  calc
    _ ≤ ∫ x, (16 ^ q * A) * lineEnvelope s l 1 x :=
      integral_mono (((polynomialLocalization a r q f).memLp 2 volume).integrable_norm_pow
        (by decide : 2 ≠ 0)) ((integrable_lineEnvelope_one s l hl).const_mul _) hpoint
    _ = _ := by rw [integral_const_mul, integral_lineEnvelope_one s l hl]

end LipschitzHilbert

end

end OAI
