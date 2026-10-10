import OAI.Combinatorics.Progressions.Estimates.ActiveAveragedProfileComparison
import OAI.Combinatorics.Progressions.Probability.AnisotropicCanonicalDensity

namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) [Fintype Z] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)

omit [Fintype Z] in
theorem activeScaledIdeal_bounds (R : (Σ d, O d) → ℝ) {C : ℝ≥0}
    (hR : ∀ i, |(R i)⁻¹| ≤ C) (δ : ℝ≥0) (hδ : 0 < δ) :
    (∀ v, |diagonalImageDensity R
      (activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ) v| ≤
        (∏ i, |R i|)⁻¹ * (δ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    LipschitzWith (‖(∏ i, |R i|)⁻¹‖₊ * (affineProductProfileLip (Σ d, O d) δ * C))
      (diagonalImageDensity R (activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ)) := by
  have hs := activeAveragedProfileIdeal_spec (G := G) (B := B) Z h P sets δ hδ
  refine ⟨diagonalImageDensity_bound R _ (fun v => ?_),
    diagonalImageDensity_lipschitz R _ hs.2.1 hR⟩
  rw [abs_of_nonneg (hs.1 v).1]
  exact (hs.1 v).2

theorem activeScaledIdeal_zero_outside (R : (Σ d, O d) → ℝ)
    (hR : ∀ i, R i ≠ 0) {C : ℝ} (hC : 0 ≤ C) (hRC : ∀ i, |R i| ≤ C)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (v : (Σ d, O d) → ℝ) (hv : C * (partitionedIdealRadius α degree + 1) < ‖v‖) :
    diagonalImageDensity R (activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ) v = 0 :=
  diagonalImageDensity_zero_outside R hR _ hC hRC
    (activeAveragedProfileIdeal_zero_outside (G := G) (B := B) Z h P sets hdegree δ hδ hδ1) v hv

end Erdos3

end

end OAI
