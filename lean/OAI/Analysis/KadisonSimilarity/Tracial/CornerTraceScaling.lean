import OAI.Analysis.BoundedHochschild.RelativeQuantization

namespace OAI

/-! Undo normalization of a corner trace in the two inequalities used by patching. -/

noncomputable section
namespace KadisonSimilarity
open HochschildCorners
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (p : A) (hp : IsStarProjection p) (τ : A →ₚ[ℂ] ℂ) (ht : 0 < (τ p).re)

include ht

theorem original_trace_lt_of_corner {q : Corner p hp} {η : ℝ}
    (h : (cornerTrace p hp τ q).re < η / (τ p).re) : (τ (q : A)).re < η := by
  rw [HochschildQuantization.corner_trace_re] at h
  have hh := mul_lt_mul_of_pos_left h ht
  simpa only [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul,
    mul_div_cancel₀ _ ht.ne'] using hh

theorem original_norm_bound_of_corner {q a : Corner p hp} {δ : ℝ}
    (h : ‖(cornerTrace p hp τ).toPreGNS a‖ ^ 2 < δ * (cornerTrace p hp τ q).re) :
    ‖τ.toPreGNS (a : A)‖ ^ 2 < δ * (τ (q : A)).re := by
  rw [HochschildQuantization.corner_norm_sq, HochschildQuantization.corner_trace_re] at h
  have hh := mul_lt_mul_of_pos_left h ht
  have hl (r : ℝ) : (τ p).re * ((τ p).re⁻¹ * r) = r := by
    rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  have hr (r : ℝ) : (τ p).re * (δ * ((τ p).re⁻¹ * r)) = δ * r := by
    field_simp [ht.ne']
  rwa [hl, hr] at hh

end KadisonSimilarity

end

end OAI
