import OAI.Geometry.NodalSets.Charts.SphereIntegratedFormComparison

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff
noncomputable section

lemma positive_ratio_relative_bounds {E F D G eps : ℝ}
    (hE : 0 ≤ E) (hD : 0 < D) (hG : 0 < G) (heps : 0 ≤ eps) (heps1 : eps < 1)
    (hlo : (1-eps)*E ≤ F) (hhi : F ≤ (1+eps)*E)
    (hdlo : (1-eps)*D ≤ G) (hdhi : G ≤ (1+eps)*D) :
    (1-eps)/(1+eps)*(E/D) ≤ F/G ∧ F/G ≤ (1+eps)/(1-eps)*(E/D) := by
  constructor
  · calc
      _ = ((1-eps)*E)/((1+eps)*D) := div_mul_div_comm _ _ _ _
      _ ≤ ((1-eps)*E)/G := div_le_div_of_nonneg_left
        (mul_nonneg (by linarith) hE) hG hdhi
      _ ≤ F/G := div_le_div_of_nonneg_right hlo hG.le
  · calc
      _ ≤ ((1+eps)*E)/G := div_le_div_of_nonneg_right hhi hG.le
      _ ≤ ((1+eps)*E)/((1-eps)*D) := div_le_div_of_nonneg_left
        (mul_nonneg (by linarith) hE) (mul_pos (by linarith) hD) hdlo
      _ = _ := (div_mul_div_comm _ _ _ _).symm

theorem sphere_finite_norm_rayleigh_comparison (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z = x)
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hAs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hAp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ eta > 0, ∀ (B : IntrinsicTensor) (sigma : Base → ℝ),
      IntrinsicTensorSmooth B → (∀ x alpha beta, B x alpha beta = B x beta alpha) →
      (∀ x alpha, alpha ≠ 0 → 0 < B x alpha alpha) →
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ sigma → (∀ x, 0 < sigma x) →
      sphereCoefficientDistance P 0 A rho B sigma < eta →
      ∀ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u → u ≠ 0 →
        (1-eps)/(1+eps)*sphereRayleighQuotient A rho u ≤ sphereRayleighQuotient B sigma u ∧
        sphereRayleighQuotient B sigma u ≤ (1+eps)/(1-eps)*sphereRayleighQuotient A rho u := by
  obtain ⟨eta,heta,hcomp⟩ := sphere_coefficient_relative_form_comparison P hcover A hA hAs hAp rho hr hrp eps heps
  refine ⟨eta,heta,?_⟩
  intro B sigma hB hBs hBp hsig hsigp hdist u hu hune
  obtain ⟨hlo,hhi,hdlo,hdhi⟩ := sphere_integrated_form_comparison A B hA hB hAs hBs hAp hBp
    rho sigma hr.continuous hsig.continuous eps (hcomp B sigma hB hBs hBp hsig hdist) u hu
  exact positive_ratio_relative_bounds (sphereDirichletForm_nonneg A hAp u)
    (sphereWeightedPairing_self_pos rho u hr.continuous hrp hu.continuous hune)
    (sphereWeightedPairing_self_pos sigma u hsig.continuous hsigp hu.continuous hune)
    heps.le heps1 hlo hhi hdlo hdhi

end
end Yau.Target

end OAI
