import OAI.GroupTheory.PolycyclicRecognition.Analysis.LipschitzReplacement
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PerturbedInversePairs

namespace OAI

/-! # Uniform Lipschitz replacement of coarse inverse pairs -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

theorem exists_lipschitz_pair_replacement_constants
    {G : Type*} [Group G] [MetricSpace G] [ProperSpace G] [IsIsometricSMul G G]
    (c : ControlledContraction G)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K C A : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) ∧ ∃ E : ℝ, 0 ≤ E ∧
      ∀ f g : G → G,
        (∀ x y, dist (f x) (f y) ≤ K * dist x y + C) →
        (∀ x y, dist (g x) (g y) ≤ K * dist x y + C) →
        (∀ x, dist (g (f x)) x ≤ A) → (∀ x, dist (f (g x)) x ≤ A) →
        ∃ p : C(G, G) × C(G, G), LipschitzPairBounds G Λ p ∧
          (∀ x, dist (p.1 x) (f x) ≤ E) ∧ (∀ x, dist (p.2 x) (g x) ≤ E) := by
  obtain ⟨L, E, hE, hrep⟩ := exists_lipschitz_replacement_constants c (1 : G) hpath hK hC
  let B := E + (K * E + C) + A
  let Λ : ℝ≥0 := ⟨max 2 (max (L : ℝ) B), le_trans (by norm_num) (le_max_left _ _)⟩
  have hΛ : 2 ≤ (Λ : ℝ) := le_max_left _ _
  have hLΛ : L ≤ Λ := (le_max_left (L : ℝ) B).trans (le_max_right _ _)
  have hBΛ : B ≤ (Λ : ℝ) := (le_max_right (L : ℝ) B).trans (le_max_right _ _)
  refine ⟨Λ, hΛ, E, hE, ?_⟩
  intro f g hf hg hgf hfg
  obtain ⟨f', hf', hff'⟩ := hrep f hf
  obtain ⟨g', hg', hgg'⟩ := hrep g hg
  have hgf' : ∀ x, dist (g' (f' x)) x ≤ Λ := fun x =>
    (inverse_error_of_bounded_perturbations f f' g g' hK hg hff' hgg' hgf x).trans hBΛ
  have hfg' : ∀ x, dist (f' (g' x)) x ≤ Λ := fun x =>
    (inverse_error_of_bounded_perturbations g g' f f' hK hf hgg' hff' hfg x).trans hBΛ
  exact ⟨(f', g'), lipschitzPairBounds_of_inverse_bounds hΛ (f', g')
    (hf'.weaken hLΛ) (hg'.weaken hLΛ) hgf' hfg', hff', hgg'⟩

end PolycyclicRecognition

end

end OAI
