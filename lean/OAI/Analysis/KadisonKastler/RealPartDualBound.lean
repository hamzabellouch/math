import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! # Recovering a functional norm from its real part on a ball -/

namespace KadisonKastler

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_mul_le_of_real_bound (f : E →L[ℂ] ℂ) {r C : ℝ} (hr : 0 < r)
    (h : ∀ x : E, ‖x‖ ≤ r → (f x).re ≤ C) : r * ‖f‖ ≤ C := by
  let g := (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)).symm f
  have hC : 0 ≤ C := by simpa using h 0 (by simpa using hr.le)
  have hnorm : ‖g‖ ≤ C / r := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hC hr.le)
    intro x hx
    have hp : r * g x ≤ C := by
      have hh := h (r • x) (by simp [norm_smul, abs_of_pos hr, hx])
      change g (r • x) ≤ C at hh
      simpa only [map_smul, smul_eq_mul] using hh
    have hn : -(r * g x) ≤ C := by
      have hh := h (r • (-x)) (by simp [norm_smul, abs_of_pos hr, hx])
      change g (r • (-x)) ≤ C at hh
      simpa only [map_smul, map_neg, smul_eq_mul, mul_neg] using hh
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have hh : -g x ≤ C / r := (le_div_iff₀ hr).mpr (by nlinarith)
      linarith
    · apply (le_div_iff₀ hr).mpr
      nlinarith
  have he : ‖g‖ = ‖f‖ := (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)).symm.norm_map f
  rw [he] at hnorm
  nlinarith [(le_div_iff₀ hr).mp hnorm]

end

end KadisonKastler

end OAI
