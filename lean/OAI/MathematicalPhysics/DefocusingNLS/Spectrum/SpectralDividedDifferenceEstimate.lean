import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! A derivative estimate controls normalized differences of nearby
spectral operator values. -/

open Set
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem spectral_divided_difference_estimate (f f' : ℂ → E) (D : E)
    (s : Set ℂ) (hs : Convex ℝ s) (ε : ℝ)
    (hf : ∀ z ∈ s, HasDerivAt f (f' z) z)
    (hbound : ∀ z ∈ s, ‖f' z-D‖ ≤ ε)
    (x y : ℂ) (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    ‖(x-y)⁻¹ • (f x-f y)-D‖ ≤ ε := by
  let g := fun z => f z-z • D
  have hg (z : ℂ) (hz : z ∈ s) : HasDerivAt g (f' z-D) z := by
    have he : g = f - (fun t : ℂ => t • D) := by funext t; rfl
    rw [he]
    simpa only [one_smul,id_eq] using (hf z hz).sub ((hasDerivAt_id z).smul_const D)
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hg z hz).hasDerivWithinAt) hbound hs hy hx
  have hd : x-y ≠ 0 := sub_ne_zero.mpr hne
  have he : g x-g y = (f x-f y)-(x-y) • D := by
    simp only [g,sub_smul]
    abel
  have he' : (x-y)⁻¹ • (g x-g y) = (x-y)⁻¹ • (f x-f y)-D := by
    rw [he,smul_sub,smul_smul,inv_mul_cancel₀ hd,one_smul]
  rw [← he',norm_smul]
  calc
    ‖(x-y)⁻¹‖ * ‖g x-g y‖ ≤ ‖(x-y)⁻¹‖ * (ε * ‖x-y‖) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ε := by rw [norm_inv]; field_simp [norm_ne_zero_iff.mpr hd]

end DefocusingNLS

end OAI
