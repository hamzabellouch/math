import Mathlib

namespace OAI

universe u_1 u_2

noncomputable section

open scoped BigOperators

namespace Problem336AdditiveD139

theorem covariance_direction_bound {F : Type u_1} [Fintype F]
    (c v : F → ℝ) (D C : ℝ) (hD : 0 ≤ D)
    (hv : ∀ j, |v j| ≤ D) (hc : ∑ j, |c j| ≤ C) :
    |∑ j, c j * v j| ≤ C * D := by
  calc
    |∑ j, c j * v j| ≤ ∑ j, |c j * v j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |c j| * |v j| := by simp only [abs_mul]
    _ ≤ ∑ j, |c j| * D := by
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
    _ = (∑ j, |c j|) * D := by rw [Finset.sum_mul]
    _ ≤ C * D := mul_le_mul_of_nonneg_right hc hD

theorem finite_response_lipschitz_of_directional_deriv
    {F : Type u_2} [Fintype F]
    (f : (F → ℝ) → ℝ) (c : (F → ℝ) → F → ℝ) (C : ℝ)
    (hderiv : ∀ (h v : F → ℝ) (t : ℝ),
      HasDerivAt (fun s : ℝ => f (fun j => h j + s * v j))
        (∑ j, c (fun k => h k + t * v k) j * v j) t)
    (hrow : ∀ h : F → ℝ, ∑ j, |c h j| ≤ C)
    (h h' : F → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hdist : ∀ j, |h j - h' j| ≤ D) :
    |f h - f h'| ≤ C * D := by
  let v : F → ℝ := fun j => h j - h' j
  have hsegment :
      ‖f (fun j => h' j + 1 * v j) - f (fun j => h' j + 0 * v j)‖ ≤ C * D := by
    apply norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t _ => (hderiv h' v t).hasDerivWithinAt)
    intro t _
    rw [Real.norm_eq_abs]
    exact covariance_direction_bound _ v D C hD hdist (hrow _)
  simpa [v, Real.norm_eq_abs] using hsegment

end Problem336AdditiveD139

end

end OAI
