import OAI.Analysis.Unitarizability.SphereNet
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace OAI

/-! Finite quarter-net tests imply the operator bound 10
for real operators. -/
noncomputable section
namespace Dixmier
namespace SphereNet
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

/-- The two quarter-net errors each cost at most a quarter of the
operator norm. Tests bounded by 5 therefore give operator norm at most 10. -/
theorem operator_norm_le_ten (M : E →L[ℝ] F) (s : Finset E) (t : Finset F)
    (_hs : ∀ x ∈ s, ‖x‖ = 1) (ht : ∀ y ∈ t, ‖y‖ = 1)
    (hsnet : ∀ x : E, ‖x‖ = 1 → ∃ x₀ ∈ s, ‖x-x₀‖ ≤ (1/4 : ℝ))
    (htnet : ∀ y : F, ‖y‖ = 1 → ∃ y₀ ∈ t, ‖y-y₀‖ ≤ (1/4 : ℝ))
    (hM : ∀ x ∈ s, ∀ y ∈ t, |inner ℝ (M x) y| ≤ 5) : ‖M‖ ≤ 10 := by
  have hb : ‖M‖ ≤ 5 + ‖M‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
    intro x y hx hy
    obtain ⟨x₀, hx₀, hdx⟩ := hsnet x hx
    obtain ⟨y₀, hy₀, hdy⟩ := htnet y hy
    have heq : inner ℝ (M x) y = inner ℝ (M x₀) y₀ +
        inner ℝ (M x) (y-y₀) + inner ℝ (M (x-x₀)) y₀ := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h1 : |inner ℝ (M x) (y-y₀)| ≤ ‖M‖/4 := by
      calc
        _ ≤ ‖M x‖ * ‖y-y₀‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
        _ ≤ (‖M‖ * ‖x‖) * (1/4) := mul_le_mul (M.le_opNorm x) hdy
          (norm_nonneg _) (mul_nonneg (norm_nonneg M) (norm_nonneg x))
        _ = _ := by rw [hx]; ring
    have h2 : |inner ℝ (M (x-x₀)) y₀| ≤ ‖M‖/4 := by
      calc
        _ ≤ ‖M (x-x₀)‖ * ‖y₀‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
        _ = ‖M (x-x₀)‖ := by rw [ht y₀ hy₀, mul_one]
        _ ≤ ‖M‖ * ‖x-x₀‖ := M.le_opNorm _
        _ ≤ ‖M‖ * (1/4) := mul_le_mul_of_nonneg_left hdx (norm_nonneg M)
        _ = _ := by ring
    change inner ℝ (M x) y ≤ 5 + ‖M‖/2
    rw [heq]
    linarith [le_abs_self (inner ℝ (M x₀) y₀), hM x₀ hx₀ y₀ hy₀,
      le_abs_self (inner ℝ (M x) (y-y₀)), le_abs_self (inner ℝ (M (x-x₀)) y₀)]
  linarith

end SphereNet
end Dixmier

end

end OAI
