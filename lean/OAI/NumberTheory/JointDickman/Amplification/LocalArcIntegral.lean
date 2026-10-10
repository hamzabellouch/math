import OAI.NumberTheory.JointDickman.Counting.SmallMajorCoefficient
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! # The exact Jacobian in the small-major-arc representation -/

namespace JointDickman
open MeasureTheory

theorem local_arc_change_variables {j X : ℝ} (hj : j ≠ 0) (hX : X ≠ 0)
    (c R : ℝ) (F : ℝ → ℂ) :
    (∫ ξ in -R..R, F (c+ξ/(j*X))) =
      ((j*X : ℝ) : ℂ)*(∫ θ in c-R/(j*X)..c+R/(j*X), F θ) := by
  have h := intervalIntegral.integral_comp_add_div (f := F) (a := -R) (b := R)
    (mul_ne_zero hj hX) c
  simpa only [neg_div,← sub_eq_add_neg,Complex.real_smul] using h

/-- The X in the published coefficient main term cancels its part of the
arc Jacobian, leaving precisely the manuscript's factor k B / j. -/
theorem local_arc_main_term {j X : ℝ} (hj : j ≠ 0) (hX : X ≠ 0)
    (c R kB B : ℝ) (a : ℂ) (F W : ℝ → ℂ) :
    ((kB*B : ℝ) : ℂ)*
      (∫ θ in c-R/(j*X)..c+R/(j*X),
        F θ*((X : ℂ)*a*W ((θ-c)*(j*X)))) =
      ((kB*B/j : ℝ) : ℂ)*a*
        (∫ ξ in -R..R, F (c+ξ/(j*X))*W ξ) := by
  have he : (fun ξ : ℝ =>
      (fun θ => F θ*((X : ℂ)*a*W ((θ-c)*(j*X)))) (c+ξ/(j*X))) =
      (fun ξ => ((X : ℂ)*a)*(F (c+ξ/(j*X))*W ξ)) := by
    funext ξ
    dsimp only
    have hx : (c+ξ/(j*X)-c)*(j*X) = ξ := by field_simp; ring
    rw [hx]
    ring
  have hc := local_arc_change_variables hj hX c R
    (fun θ => F θ*((X : ℂ)*a*W ((θ-c)*(j*X))))
  rw [he,intervalIntegral.integral_const_mul] at hc
  have hjc : (j : ℂ) ≠ 0 := by exact_mod_cast hj
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  push_cast at hc ⊢
  have hs := congrArg (fun z : ℂ => ((kB : ℂ)*B/(j*X))*z) hc
  field_simp at hs ⊢
  linear_combination -hs

end JointDickman

end OAI
