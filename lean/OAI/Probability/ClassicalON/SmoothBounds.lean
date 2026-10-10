import OAI.Probability.ClassicalON.SmoothProfiles

namespace OAI

universe uE uF

noncomputable section
open Set Function
open scoped ContDiff
namespace ClassicalON

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem compact_continuous_norm_bound {f : E → F} (hc : HasCompactSupport f) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C,hC⟩ := (hc.isCompact_range hf).isBounded.exists_norm_le
  exact ⟨max C 0, le_max_right _ _, fun x => (hC _ ⟨x,rfl⟩).trans (le_max_left _ _)⟩

theorem smooth_compact_lipschitz_bound {f : E → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ‖f x‖ ≤ C) ∧
      (∀ x y, ‖f y-f x‖ ≤ C*‖y-x‖) := by
  obtain ⟨A,hA,hfA⟩ := compact_continuous_norm_bound hc hf.continuous
  obtain ⟨B,hB,hfB⟩ := compact_continuous_norm_bound (hc.fderiv ℝ)
    (hf.fderiv_right (m := ∞) (by simp)).continuous
  refine ⟨A+B, add_nonneg hA hB, fun x => (hfA x).trans (le_add_of_nonneg_right hB), ?_⟩
  intro x y
  calc ‖f y-f x‖ ≤ B*‖y-x‖ :=
        Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf.differentiable (by simp) z)
          (fun z _ => hfB z) convex_univ (mem_univ x) (mem_univ y)
       _ ≤ (A+B)*‖y-x‖ := by gcongr; exact le_add_of_nonneg_left hA

theorem scalar_lipschitz_of_deriv_bound (f f' : ℝ → ℝ) (C : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hC : ∀ x, |f' x| ≤ C) (x y : ℝ) :
    |f y-f x| ≤ C*|y-x| := by
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hf z).hasDerivWithinAt) (fun z _ => hC z) convex_univ
      (mem_univ x) (mem_univ y)

theorem abs_sub_left_le_of_uIcc {x y z : ℝ} (hz : z ∈ uIcc x y) :
    |z-x| ≤ |y-x| := by
  rcases le_total x y with h | h
  · rw [uIcc_of_le h] at hz
    rw [abs_of_nonneg (sub_nonneg.mpr hz.1), abs_of_nonneg (sub_nonneg.mpr h)]
    linarith [hz.2]
  · rw [uIcc_of_ge h] at hz
    rw [abs_of_nonpos (sub_nonpos.mpr hz.2), abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [hz.1]

theorem first_remainder_bound (f f' : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hL : ∀ x y, |f' y-f' x| ≤ C*|y-x|) (x y : ℝ) :
    |f y-f x-f' x*(y-x)| ≤ C*|y-x|^2 := by
  let g := fun z => f z-f' x*z
  have hg (z : ℝ) : HasDerivAt g (f' z-f' x) z := by
    convert (hf z).sub ((hasDerivAt_id z).const_mul (f' x)) using 1 <;> first | rfl | ring
  have hb (z : ℝ) (hz : z ∈ uIcc x y) : |f' z-f' x| ≤ C*|y-x| :=
    (hL x z).trans (mul_le_mul_of_nonneg_left (abs_sub_left_le_of_uIcc hz) hC)
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ uIcc x y) => (hg z).hasDerivWithinAt)
    (fun z hz => hb z hz) (convex_uIcc x y) (left_mem_uIcc) (right_mem_uIcc)
  change |g y-g x| ≤ _ at H
  convert H using 1
  · congr 1; ring
  · rw [Real.norm_eq_abs]; ring

theorem second_remainder_bound (f f' f'' : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hL : ∀ x y, |f'' y-f'' x| ≤ C*|y-x|) (x y : ℝ) :
    |f y-f x-f' x*(y-x)-f'' x/2*(y-x)^2| ≤ C*|y-x|^3 := by
  let g := fun z => f z-f' x*(z-x)-f'' x/2*(z-x)^2
  have hg (z : ℝ) : HasDerivAt g (f' z-f' x-f'' x*(z-x)) z := by
    have ht : HasDerivAt (fun t : ℝ => t-x) 1 z := (hasDerivAt_id z).sub_const x
    have hq := ((hf z).sub (ht.const_mul (f' x))).sub ((ht.pow 2).const_mul (f'' x/2))
    convert hq using 1; first | rfl | ring
  have hb (z : ℝ) (hz : z ∈ uIcc x y) : |f' z-f' x-f'' x*(z-x)| ≤ C*|y-x|^2 := by
    exact (first_remainder_bound f' f'' C hC hf' hL x z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (abs_sub_left_le_of_uIcc hz) 2) hC)
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ uIcc x y) => (hg z).hasDerivWithinAt)
    (fun z hz => hb z hz) (convex_uIcc x y) (left_mem_uIcc) (right_mem_uIcc)
  change |g y-g x| ≤ _ at H
  convert H using 1
  · congr 1; ring
  · rw [Real.norm_eq_abs]; ring

theorem trapezoid_error_bound (f f' f'' : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hL : ∀ x y, |f'' y-f'' x| ≤ C*|y-x|) (x y : ℝ) :
    |f y-f x-(y-x)/2*(f' x+f' y)| ≤ 2*C*|y-x|^3 := by
  have h1 := second_remainder_bound f f' f'' C hC hf hf' hL x y
  have h2 := first_remainder_bound f' f'' C hC hf' hL x y
  have he : f y-f x-(y-x)/2*(f' x+f' y) =
      (f y-f x-f' x*(y-x)-f'' x/2*(y-x)^2) -
        (y-x)/2*(f' y-f' x-f'' x*(y-x)) := by ring
  rw [he]
  calc _ ≤ |f y-f x-f' x*(y-x)-f'' x/2*(y-x)^2| +
        |(y-x)/2*(f' y-f' x-f'' x*(y-x))| := abs_sub _ _
       _ ≤ C*|y-x|^3+|y-x|/2*(C*|y-x|^2) := by
          rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
          gcongr
       _ ≤ _ := by nlinarith [mul_nonneg hC (pow_nonneg (abs_nonneg (y-x)) 3)]

end ClassicalON

end

end OAI
