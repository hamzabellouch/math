import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI

/-! # Monotone finite-difference bounds for positive Riesz weights -/
namespace JointDickman
open Finset

theorem hinge_difference_bounds {a x y t : ℝ} (ha : 0 ≤ a) (hxy : x ≤ y) :
    (y-x)*(if t ≤ x then a else 0) ≤ a*(max (y-t) 0-max (x-t) 0) ∧
    a*(max (y-t) 0-max (x-t) 0) ≤ (y-x)*(if t ≤ y then a else 0) := by
  by_cases htx : t ≤ x
  · have hty : t ≤ y := htx.trans hxy
    rw [ite_eq_left htx,ite_eq_left hty,max_eq_left (by linarith : 0 ≤ y-t),
      max_eq_left (by linarith : 0 ≤ x-t)]
    constructor <;> nlinarith
  · by_cases hty : t ≤ y
    · rw [ite_eq_right htx,ite_eq_left hty,max_eq_left (by linarith : 0 ≤ y-t),
        max_eq_right (by linarith : x-t ≤ 0)]
      constructor <;> nlinarith
    · rw [ite_eq_right htx,ite_eq_right hty,max_eq_right (by linarith : y-t ≤ 0),
        max_eq_right (by linarith : x-t ≤ 0)]
      simp

theorem finite_riesz_difference_bounds {ι : Type*} (s : Finset ι) (a t : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) {x y : ℝ} (hxy : x ≤ y) :
    (y-x)*(∑ i ∈ s, if t i ≤ x then a i else 0) ≤
        (∑ i ∈ s, a i*max (y-t i) 0) - (∑ i ∈ s, a i*max (x-t i) 0) ∧
    (∑ i ∈ s, a i*max (y-t i) 0) - (∑ i ∈ s, a i*max (x-t i) 0) ≤
        (y-x)*(∑ i ∈ s, if t i ≤ y then a i else 0) := by
  rw [←sum_sub_distrib,mul_sum,mul_sum]
  constructor
  · apply sum_le_sum
    intro i hi
    simpa only [mul_sub] using (hinge_difference_bounds (ha i hi) hxy (t := t i)).1
  · apply sum_le_sum
    intro i hi
    simpa only [mul_sub] using (hinge_difference_bounds (ha i hi) hxy (t := t i)).2

end JointDickman

end OAI
