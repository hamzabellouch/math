import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

namespace OAI

/-! # Quantitative finite-difference recovery from a Riesz primitive -/
namespace JointDickman
open Set

theorem secant_error_of_second_derivative {f g g' : ℝ → ℝ} {a b x M : ℝ}
    (hab : a ≤ b) (hx : x ∈ Icc a b) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hbound : ∀ t ∈ Icc a b, |g' t| ≤ M) :
    |f b-f a-g x*(b-a)| ≤ M*(b-a)^2 := by
  have hconv : Convex ℝ (Icc a b) := convex_Icc a b
  have hvar : ∀ t ∈ Icc a b, ‖g t-g x‖ ≤ M*(b-a) := by
    intro t ht
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hg u hu).hasDerivWithinAt)
      (fun u hu => by simpa only [Real.norm_eq_abs] using hbound u hu) hconv hx ht
    have hdist : ‖t-x‖ ≤ b-a := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hx.2,ht.1],by linarith [hx.1,ht.2]⟩
    exact h.trans (mul_le_mul_of_nonneg_left hdist hM)
  have hderiv : ∀ t ∈ Icc a b, HasDerivAt (fun u => f u-g x*u) (g t-g x) t := by
    intro t ht
    convert (hf t ht).sub ((hasDerivAt_id t).const_mul (g x)) using 1 <;>
      first | rfl | simp only [mul_one]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hvar hconv
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] at h
  have heq : (f b-g x*b)-(f a-g x*a) = f b-f a-g x*(b-a) := by ring
  rw [heq] at h
  nlinarith

theorem unsmooth_from_secants {F S : ℝ → ℝ} {A g x h E M : ℝ}
    (hh : 0 < h)
    (hminus : F x-F (x-h) ≤ h*A)
    (hplus : h*A ≤ F (x+h)-F x)
    (he₀ : |F x-S x| ≤ E)
    (heMinus : |F (x-h)-S (x-h)| ≤ E)
    (hePlus : |F (x+h)-S (x+h)| ≤ E)
    (hsMinus : |S x-S (x-h)-g*h| ≤ M*h^2)
    (hsPlus : |S (x+h)-S x-g*h| ≤ M*h^2) :
    |A-g| ≤ M*h+2*E/h := by
  have e₀ := abs_le.mp he₀
  have eMinus := abs_le.mp heMinus
  have ePlus := abs_le.mp hePlus
  have sMinus := abs_le.mp hsMinus
  have sPlus := abs_le.mp hsPlus
  have hhi : h*(A-g) ≤ M*h^2+2*E := by linarith [e₀.1,ePlus.2,sPlus.2]
  have hlo : -(M*h^2+2*E) ≤ h*(A-g) := by linarith [e₀.2,eMinus.1,sMinus.1]
  have heq : h*(M*h+2*E/h) = M*h^2+2*E := by field_simp
  rw [←heq] at hhi hlo
  apply abs_le.mpr
  constructor <;> nlinarith

end JointDickman

end OAI
