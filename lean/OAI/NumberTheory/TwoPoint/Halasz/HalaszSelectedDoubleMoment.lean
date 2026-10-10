import OAI.NumberTheory.TwoPoint.Halasz.HalaszNormalizedDoubleMoment

namespace OAI

/-! The sole selected moment needed for logarithmic exponential sums. -/
namespace TwoPointCorrelations

open Finset

def halaszSelectedMoment (k : ℕ) : ℕ := (10*k+1)*k

lemma halasz_selected_moment_pos {k : ℕ} (hk : 2≤k) : 1≤halaszSelectedMoment k := by
  unfold halaszSelectedMoment
  nlinarith

theorem halasz_selected_double_moment : ∃ R₀ : ℕ, ∀ k : ℕ, 2≤k →
    ∀ M : ℕ, 1≤M → ∀ γ : Fin k → ℝ, (∀ j,γ j≠0) →
    ‖∑ b : Fin M,halaszVinogradovPolynomial k M
      (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^
        (2*halaszSelectedMoment k*halaszSelectedMoment k) ≤
      (32*(halaszSelectedMoment k:ℝ))^k*(R₀+k+32:ℝ)^(512*k^4)*
        (M:ℝ)^(4*(halaszSelectedMoment k:ℝ)^2+(k:ℝ)^2/1024)*
          ∏ j,halaszNormalizedWeight (halaszSelectedMoment k) M γ j := by
  obtain ⟨R₀,hR⟩ := halasz_quantitative_mean_value
  refine ⟨R₀,?_⟩
  intro k hk M hM γ hγ
  have hJ := hR k hk M hM
  rw [← halasz_coordinate_total_degree (by omega : 0<k)] at hJ
  have h := halasz_normalized_double_moment (halasz_selected_moment_pos hk) hM γ hγ
    (C := (R₀+k+32:ℝ)^(256*k^4)) (ε := (k:ℝ)^2/2048) hJ
  convert h using 1
  have he : 2*((k:ℝ)^2/2048)=(k:ℝ)^2/1024 := by ring
  rw [he,← pow_mul,show (256*k^4)*2=512*k^4 by omega]

end TwoPointCorrelations

end OAI
