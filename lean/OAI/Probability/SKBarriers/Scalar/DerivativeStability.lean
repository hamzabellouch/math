import Mathlib

namespace OAI

section

section
noncomputable section
open scoped Topology NNReal
namespace SK.Analytic

theorem derivative_bound_of_uniform_value_and_lipschitz
    (f f' : ℝ → ℝ) (K : ℝ≥0) (ε : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hK : LipschitzWith K f')
    (hε : ∀ x, |f x| ≤ ε) (x h : ℝ) (hh : 0 < h) :
    |f' x| ≤ 2*ε/h+(K:ℝ)*h := by
  let F := fun t : ℝ => f t-f' x*t
  have hF (t : ℝ) : HasDerivAt F (f' t-f' x) t := by
    convert (hf t).sub ((hasDerivAt_id t).const_mul (f' x)) using 1 <;>
      first | rfl | simp only [mul_one]
  have hb (t : ℝ) (ht : t ∈ Set.Icc x (x+h)) : ‖f' t-f' x‖ ≤ (K:ℝ)*h := by
    have H := hK.norm_sub_le t x
    apply H.trans
    apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have H := (convex_Icc x (x+h)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hF t).hasDerivWithinAt) hb
    (show x ∈ Set.Icc x (x+h) from ⟨le_rfl,by linarith⟩)
    (show x+h ∈ Set.Icc x (x+h) from ⟨by linarith,le_rfl⟩)
  have he : F (x+h)-F x = f (x+h)-f x-f' x*h := by dsimp [F]; ring
  rw [he,Real.norm_eq_abs,Real.norm_eq_abs,add_sub_cancel_left,abs_of_pos hh] at H
  have hy := abs_le.mp (hε (x+h))
  have hx := abs_le.mp (hε x)
  have hE := abs_le.mp H
  have H' : |f' x*h| ≤ 2*ε+(K:ℝ)*h*h := by
    rw [abs_le]
    constructor <;> linarith
  rw [abs_mul,abs_of_pos hh] at H'
  have HD := (le_div_iff₀ hh).mpr H'
  apply HD.trans_eq
  rw [add_div,mul_div_cancel_right₀ _ hh.ne']

end SK.Analytic

end
end

end

end OAI
