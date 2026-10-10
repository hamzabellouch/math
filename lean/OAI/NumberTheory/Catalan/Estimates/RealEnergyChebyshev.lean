import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace InternalCatalan

section

theorem energy_chord_sq_identity (ζ : ℂ) (hζ : ‖ζ‖ = 1) (r : ℝ) :
    ‖(1 : ℂ) - (r : ℂ) * ζ‖ ^ 2 - r * ‖(1 : ℂ) - ζ‖ ^ 2 = (1 - r) ^ 2 := by
  have hζsq : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hζ, one_pow]
  simp only [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one,
    Complex.normSq_mul, Complex.normSq_ofReal, hζsq, one_mul, mul_one,
    Complex.conj_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

theorem energy_chord_sq_le (ζ : ℂ) (hζ : ‖ζ‖ = 1) (r : ℝ) :
    r * ‖(1 : ℂ) - ζ‖ ^ 2 ≤ ‖(1 : ℂ) - (r : ℂ) * ζ‖ ^ 2 := by
  have hid := energy_chord_sq_identity ζ hζ r
  nlinarith [sq_nonneg (1 - r)]

theorem energy_damped_chord_pos (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1)
    {r : ℝ} (hr : 0 < r) : 0 < ‖(1 : ℂ) - (r : ℂ) * ζ‖ := by
  have horig : 0 < ‖(1 : ℂ) - ζ‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hζ1.symm)
  have hsquare : 0 < ‖(1 : ℂ) - (r : ℂ) * ζ‖ ^ 2 :=
    lt_of_lt_of_le (mul_pos hr (sq_pos_of_pos horig)) (energy_chord_sq_le ζ hζ r)
  nlinarith [norm_nonneg ((1 : ℂ) - (r : ℂ) * ζ)]

theorem energy_log_chord_le (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1)
    {r : ℝ} (hr : 0 < r) :
    Real.log ‖(1 : ℂ) - ζ‖ ≤
      Real.log ‖(1 : ℂ) - (r : ℂ) * ζ‖ - Real.log r / 2 := by
  have horig : 0 < ‖(1 : ℂ) - ζ‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hζ1.symm)
  have hdamped := energy_damped_chord_pos ζ hζ hζ1 hr
  have hlog := (Real.log_le_log_iff (mul_pos hr (sq_pos_of_pos horig))
    (sq_pos_of_pos hdamped)).mpr (energy_chord_sq_le ζ hζ r)
  rw [Real.log_mul hr.ne' (pow_ne_zero 2 horig.ne')] at hlog
  simp only [Real.log_pow, Nat.cast_ofNat] at hlog
  linarith

end

section

open Set
open scoped ComplexConjugate

def realEnergyCirclePoint (u : ℝ) : ℂ :=
  (u : ℂ) + Complex.I * (Real.sqrt (1 - u ^ 2) : ℂ)

theorem realEnergyCirclePoint_norm {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    ‖realEnergyCirclePoint u‖ = 1 := by
  have hn : ‖u‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using abs_le.mpr hu
  have h := Complex.normSq_ofReal_add_I_mul_sqrt_one_sub hn
  change Complex.normSq (realEnergyCirclePoint u) = 1 at h
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (realEnergyCirclePoint u)]

theorem realEnergyCirclePoint_add_conj (u : ℝ) :
    realEnergyCirclePoint u + conj (realEnergyCirclePoint u) = 2 * (u : ℂ) := by
  apply Complex.ext <;> simp [realEnergyCirclePoint]
  ring

theorem realEnergyCirclePoint_mul_conj {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    realEnergyCirclePoint u * conj (realEnergyCirclePoint u) = 1 := by
  rw [Complex.mul_conj', realEnergyCirclePoint_norm hu]
  norm_num

theorem realEnergyCirclePoint_quadratic {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    realEnergyCirclePoint u ^ 2 + 1 = 2 * (u : ℂ) * realEnergyCirclePoint u := by
  calc
    _ = realEnergyCirclePoint u *
        (realEnergyCirclePoint u + conj (realEnergyCirclePoint u)) := by
      rw [mul_add, realEnergyCirclePoint_mul_conj hu, pow_two]
    _ = _ := by rw [realEnergyCirclePoint_add_conj]; ring

theorem realEnergy_cosine_chord_product {u v : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    ‖(1 : ℂ) - realEnergyCirclePoint u * realEnergyCirclePoint v‖ *
      ‖(1 : ℂ) - realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ =
      2 * |u - v| := by
  have hc :
      ((1 : ℂ) - realEnergyCirclePoint u * realEnergyCirclePoint v) *
        ((1 : ℂ) - realEnergyCirclePoint u * conj (realEnergyCirclePoint v)) =
      2 * realEnergyCirclePoint u * ((u : ℂ) - (v : ℂ)) := by
    calc
      _ = 1 - realEnergyCirclePoint u *
          (realEnergyCirclePoint v + conj (realEnergyCirclePoint v)) +
          realEnergyCirclePoint u ^ 2 *
            (realEnergyCirclePoint v * conj (realEnergyCirclePoint v)) := by ring
      _ = (realEnergyCirclePoint u ^ 2 + 1) -
          2 * (v : ℂ) * realEnergyCirclePoint u := by
        rw [realEnergyCirclePoint_add_conj, realEnergyCirclePoint_mul_conj hv]
        ring
      _ = _ := by rw [realEnergyCirclePoint_quadratic hu]; ring
  have hh := congrArg (fun z : ℂ => ‖z‖) hc
  simpa only [Complex.norm_mul, realEnergyCirclePoint_norm hu,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, mul_one] using hh

def realEnergyCosineKernel (r u v : ℝ) : ℝ :=
  -Real.log 2 +
    Real.log ‖(1 : ℂ) - (r : ℂ) * (realEnergyCirclePoint u * realEnergyCirclePoint v)‖ +
    Real.log ‖(1 : ℂ) - (r : ℂ) * (realEnergyCirclePoint u * conj (realEnergyCirclePoint v))‖

theorem realEnergyCosineKernel_one {u v : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) (huv : u ≠ v) :
    realEnergyCosineKernel 1 u v = Real.log |u - v| := by
  have hp := realEnergy_cosine_chord_product hu hv
  have hprod :
      ‖(1 : ℂ) - realEnergyCirclePoint u * realEnergyCirclePoint v‖ *
        ‖(1 : ℂ) - realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ ≠ 0 := by
    rw [hp]
    exact mul_ne_zero (by norm_num) (abs_ne_zero.mpr (sub_ne_zero.mpr huv))
  have hl := congrArg Real.log hp
  rw [Real.log_mul (mul_ne_zero_iff.mp hprod).1 (mul_ne_zero_iff.mp hprod).2,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (abs_ne_zero.mpr (sub_ne_zero.mpr huv))] at hl
  unfold realEnergyCosineKernel
  simp only [Complex.ofReal_one, one_mul]
  linarith

theorem realEnergyCosineKernel_compare {u v r : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1)
    (huv : u ≠ v) (hr : 0 < r) :
    Real.log |u - v| ≤ realEnergyCosineKernel r u v - Real.log r := by
  have hp := realEnergy_cosine_chord_product hu hv
  have hprod :
      ‖(1 : ℂ) - realEnergyCirclePoint u * realEnergyCirclePoint v‖ *
        ‖(1 : ℂ) - realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ ≠ 0 := by
    rw [hp]
    exact mul_ne_zero (by norm_num) (abs_ne_zero.mpr (sub_ne_zero.mpr huv))
  have hn1 : ‖realEnergyCirclePoint u * realEnergyCirclePoint v‖ = 1 := by
    rw [Complex.norm_mul, realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv, one_mul]
  have hn2 : ‖realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ = 1 := by
    rw [Complex.norm_mul, Complex.norm_conj,
      realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv, one_mul]
  have hne1 : realEnergyCirclePoint u * realEnergyCirclePoint v ≠ 1 := by
    intro h
    apply (mul_ne_zero_iff.mp hprod).1
    rw [h, sub_self, norm_zero]
  have hne2 : realEnergyCirclePoint u * conj (realEnergyCirclePoint v) ≠ 1 := by
    intro h
    apply (mul_ne_zero_iff.mp hprod).2
    rw [h, sub_self, norm_zero]
  have h1 := energy_log_chord_le _ hn1 hne1 hr
  have h2 := energy_log_chord_le _ hn2 hne2 hr
  rw [← realEnergyCosineKernel_one hu hv huv]
  unfold realEnergyCosineKernel
  simp only [Complex.ofReal_one, one_mul]
  linarith

end

open Polynomial Set
open scoped ComplexConjugate

theorem realEnergyCirclePoint_pow_re (k : ℕ) {u : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    (realEnergyCirclePoint u ^ k).re = (Chebyshev.T ℝ (k : ℤ)).eval u := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simp [realEnergyCirclePoint]
  | more k ih0 ih1 =>
    have hp : realEnergyCirclePoint u ^ (k + 2) + realEnergyCirclePoint u ^ k =
        2 * (u : ℂ) * realEnergyCirclePoint u ^ (k + 1) := by
      calc
        _ = realEnergyCirclePoint u ^ k * (realEnergyCirclePoint u ^ 2 + 1) := by
          rw [pow_add]
          ring
        _ = _ := by
          rw [realEnergyCirclePoint_quadratic hu, pow_succ]
          ring
    have hr := congrArg Complex.re hp
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, sub_zero, add_zero] at hr
    have hi1 : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
    rw [Nat.cast_add, Nat.cast_ofNat, Chebyshev.T_add_two]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    rw [hi1, ← ih1, ← ih0]
    linarith

theorem energy_chebyshev_abs_le_one (k : ℕ) {u : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) : |(Chebyshev.T ℝ (k : ℤ)).eval u| ≤ 1 := by
  rw [← realEnergyCirclePoint_pow_re k hu]
  calc
    _ ≤ ‖realEnergyCirclePoint u ^ k‖ := Complex.abs_re_le_norm _
    _ = 1 := by rw [Complex.norm_pow, realEnergyCirclePoint_norm hu, one_pow]

theorem realEnergyCirclePoint_pair_pow_re (k : ℕ) {u v : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    ((realEnergyCirclePoint u * realEnergyCirclePoint v) ^ k).re +
      ((realEnergyCirclePoint u * conj (realEnergyCirclePoint v)) ^ k).re =
      2 * (Chebyshev.T ℝ (k : ℤ)).eval u * (Chebyshev.T ℝ (k : ℤ)).eval v := by
  simp only [mul_pow, ← map_pow, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [realEnergyCirclePoint_pow_re k hu, realEnergyCirclePoint_pow_re k hv]
  ring

end InternalCatalan

end

end OAI
