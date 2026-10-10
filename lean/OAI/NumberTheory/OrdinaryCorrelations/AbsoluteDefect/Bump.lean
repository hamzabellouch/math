import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Phase

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction

namespace OrdinaryGaussianWindow
open OrdinaryDirichletMeanSquare

def bump (x : ℝ) : ℝ := Real.exp (-2*x^2)

def window {ι : Type*} (s : Finset ι) (a : ι → ℂ) (u : ι → ℝ) (x : ℝ) : ℂ :=
  ∑ n ∈ s, a n * (bump (x-u n) : ℂ)

lemma bump_pair (u v x : ℝ) :
    bump (x-u) * bump (x-v) = gaussian (2*x-(u+v)) * Real.exp (-(u-v)^2) := by
  unfold bump gaussian
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma bump_pair_integrable (u v : ℝ) :
    Integrable (fun x : ℝ => bump (x-u) * bump (x-v)) := by
  simp_rw [bump_pair]
  have h := gaussian_integrable.comp_add_right (-(u+v))
  have h' := (integrable_comp_mul_left_iff (fun x : ℝ => gaussian (x-(u+v)))
    (show (2:ℝ) ≠ 0 by norm_num)).mpr (by simpa only [sub_eq_add_neg] using h)
  exact h'.mul_const _

lemma bump_pair_integral (u v : ℝ) :
    ∫ x : ℝ, ((bump (x-u) * bump (x-v) : ℝ) : ℂ) =
      (1/2:ℂ) * (Real.pi : ℂ)^(1/2:ℂ) * (Real.exp (-(u-v)^2) : ℂ) := by
  simp_rw [bump_pair, Complex.ofReal_mul]
  rw [integral_mul_const]
  have h := Measure.integral_comp_mul_left
    (fun x : ℝ => (gaussian (x-(u+v)) : ℂ)) (2:ℝ)
  rw [integral_sub_right_eq_self (fun x : ℝ => (gaussian x : ℂ)) (u+v)] at h
  have hg : ∫ x : ℝ, (gaussian x : ℂ) = (Real.pi:ℂ)^(1/2:ℂ) := by
    simpa [phase] using gaussian_phase_integral 0
  rw [h, hg]
  norm_num

lemma window_square_integrable {ι : Type*} (s : Finset ι) (a : ι → ℂ) (u : ι → ℝ) :
    Integrable (fun x : ℝ => ‖window s a u x‖^2) := by
  have hc : Continuous (fun x : ℝ => ‖window s a u x‖^2) := by
    unfold window bump
    fun_prop
  apply Integrable.mono'
    (integrable_finsetSum s fun m hm => integrable_finsetSum s fun n hn =>
      (bump_pair_integrable (u m) (u n)).const_mul (‖a m‖*‖a n‖))
    hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (∑ n ∈ s, ‖a n‖ * bump (x-u n))^2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      change ‖a n‖ * |Real.exp _| ≤ ‖a n‖ * Real.exp _
      rw [abs_of_pos (Real.exp_pos _)]
    _ = _ := by
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      ring

lemma window_energy_expansion {ι : Type*} (s : Finset ι) (a : ι → ℂ) (u : ι → ℝ) :
    (((∫ x : ℝ, ‖window s a u x‖^2) : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, (a m * star (a n)) *
        ((1/2:ℂ) * (Real.pi:ℂ)^(1/2:ℂ) * (Real.exp (-(u m-u n)^2) : ℂ)) := by
  rw [← integral_complex_ofReal]
  have he (x : ℝ) : ((‖window s a u x‖^2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, (a m * star (a n)) *
        ((bump (x-u m) * bump (x-u n) : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    unfold window
    simp only [map_sum]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  simp_rw [he]
  have hi (m n : ι) : Integrable (fun x : ℝ => (a m * star (a n)) *
      ((bump (x-u m) * bump (x-u n) : ℝ) : ℂ)) :=
    ((bump_pair_integrable (u m) (u n)).ofReal).const_mul _
  rw [integral_finsetSum s (fun m hm => integrable_finsetSum s (fun n hn => hi m n))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [integral_finsetSum s (fun n hn => hi m n)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [integral_const_mul, bump_pair_integral]

theorem gaussian_window_spectral_identity {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (u : ι → ℝ) :
    (∫ x : ℝ, ‖window s a u x‖^2) =
      (1/2:ℝ) * ∫ t : ℝ, gaussian t * ‖polynomial s a (fun n => 2*u n) t‖^2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, window_energy_expansion, gaussian_polynomial_expansion]
  simp_rw [gaussian_phase_integral, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have h : -(2*u m-2*u n)^2/4 = -(u m-u n)^2 := by ring
  rw [h]
  push_cast
  ring

end OrdinaryGaussianWindow

end

end OAI
