import OAI.NumberTheory.TwoPoint.Halasz.HalaszSmallDefect
import OAI.NumberTheory.TwoPoint.Halasz.HalaszConstantGrowth

namespace OAI

/-! The one quantitative complete-system estimate used by the subsequent
logarithmic phase argument. Both the defect and the constant are explicit. -/
namespace TwoPointCorrelations

theorem halasz_quantitative_mean_value : ∃ R₀ : ℕ, ∀ k : ℕ, 2≤k →
    ∀ N : ℕ, 1≤N →
    (halaszVinogradovCount ((10*k+1)*k) k N:ℝ) ≤
      (R₀+k+32:ℝ)^(256*k^4)*
        (N:ℝ)^(2*(((10*k+1)*k:ℕ):ℝ)-(halaszTotalDegree k:ℝ)+(k:ℝ)^2/2048) := by
  obtain ⟨R₀,hmean⟩ := halasz_classical_selected_moment
  refine ⟨R₀,?_⟩
  intro k hk N hN
  apply (hmean k hk N hN).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact_mod_cast halasz_selected_constant_growth (R₀ := R₀) hk

end TwoPointCorrelations

end OAI
