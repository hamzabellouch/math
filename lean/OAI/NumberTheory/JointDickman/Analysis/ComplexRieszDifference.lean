import OAI.NumberTheory.JointDickman.Analysis.RieszHingeBounds
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! # Bounded complex coefficients in finite Riesz differences -/
namespace JointDickman
open Finset

theorem complex_hinge_error_norm {a : ℂ} {x y t : ℝ}
    (ha : ‖a‖ ≤ 1) (hxy : x ≤ y) :
    ‖a*((max (y-t) 0-max (x-t) 0):ℝ) -
      ((y-x):ℂ)*(if t ≤ x then a else 0)‖ ≤
      if x < t ∧ t ≤ y then y-x else 0 := by
  by_cases htx : t ≤ x
  · have hty : t ≤ y := htx.trans hxy
    rw [ite_eq_left htx, ite_eq_right (by exact fun h => (not_lt_of_ge htx) h.1),
      max_eq_left (by linarith : 0 ≤ y-t), max_eq_left (by linarith : 0 ≤ x-t)]
    have he : ((y-t-(x-t):ℝ):ℂ) = (y-x:ℂ) := by push_cast; ring
    rw [he, mul_comm a, sub_self, norm_zero]
  · have hxt : x < t := lt_of_not_ge htx
    by_cases hty : t ≤ y
    · rw [ite_eq_right htx, ite_eq_left ⟨hxt,hty⟩, mul_zero, sub_zero,
        max_eq_left (by linarith : 0 ≤ y-t), max_eq_right (by linarith : x-t ≤ 0), sub_zero,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ y-t)]
      calc
        _ ≤ 1*(y-t) := mul_le_mul_of_nonneg_right ha (by linarith)
        _ ≤ _ := by linarith
    · rw [ite_eq_right htx, ite_eq_right (by exact fun h => hty h.2), mul_zero, sub_zero,
        max_eq_right (by linarith : y-t ≤ 0), max_eq_right (by linarith : x-t ≤ 0), sub_self]
      simp

theorem finite_complex_riesz_difference_bound {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (t : ι → ℝ) (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) {x y : ℝ} (hxy : x ≤ y) :
    ‖(∑ i ∈ s, a i*(max (y-t i) 0:ℝ)) -
       (∑ i ∈ s, a i*(max (x-t i) 0:ℝ)) -
       ((y-x):ℂ)*(∑ i ∈ s, if t i ≤ x then a i else 0)‖ ≤
      (s.filter (fun i => x < t i ∧ t i ≤ y)).card * (y-x) := by
  have he : (∑ i ∈ s, a i*(max (y-t i) 0:ℝ)) -
       (∑ i ∈ s, a i*(max (x-t i) 0:ℝ)) -
       ((y-x):ℂ)*(∑ i ∈ s, if t i ≤ x then a i else 0) =
      ∑ i ∈ s, (a i*((max (y-t i) 0-max (x-t i) 0):ℝ) -
        ((y-x):ℂ)*(if t i ≤ x then a i else 0)) := by
    simp only [sum_sub_distrib, mul_sum, Complex.ofReal_sub, mul_sub]
  rw [he]
  calc
    _ ≤ ∑ i ∈ s, ‖a i*((max (y-t i) 0-max (x-t i) 0):ℝ) -
        ((y-x):ℂ)*(if t i ≤ x then a i else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, if x < t i ∧ t i ≤ y then y-x else 0 :=
      sum_le_sum (fun i hi => complex_hinge_error_norm (ha i hi) hxy)
    _ = _ := by rw [←sum_filter]; simp; ring

end JointDickman

end OAI
