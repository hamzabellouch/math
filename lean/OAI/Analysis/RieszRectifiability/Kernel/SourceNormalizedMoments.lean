import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.NormalizedLocalEnergyBasic
import OAI.Analysis.RieszRectifiability.Kernel.DyadicSourceMoments

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem source_normalized_second_moments_on_ball {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (u : ℕ → Ambient d → ℝ) (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j))
    (a : Ambient d) (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ)
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j,
      MemLp (fun x => u j x / δ j) 2 ((μ j).restrict (ball a r)) ∧
      (∫ x in ball a r, (u j x / δ j) ^ 2 ∂μ j) ≤ B := by
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt r (by norm_num : (1 : ℝ) < 2)
  let B₀ := D * ((2 : ℝ) ^ q) ^ n * ((2 : ℝ) ^ q * b ^ q) ^ 2
  have hI (j : ℕ) := normalized_lipschitz_memLp_on_ball n G (μ j) (hg j) (u j) K
    (hu j) a r (δ j) hr
  have hlarge (j : ℕ) := normalized_lipschitz_memLp_on_ball n G (μ j) (hg j) (u j) K
    (hu j) a ((2 : ℝ) ^ q) (δ j) (by positivity)
  have hbound : ∀ᶠ j in atTop, (∫ x in ball a r, (u j x / δ j) ^ 2 ∂μ j) ≤ B₀ := by
    filter_upwards [hN.eventually (eventually_ge_atTop q)] with j hj
    apply (integral_mono_measure
      (Measure.restrict_mono (ball_subset_ball hq.le) le_rfl)
      (Eventually.of_forall fun x => sq_nonneg (u j x / δ j)) (hlarge j).integrable_sq).trans
    apply normalized_second_moment_bound ((μ j).restrict (ball a ((2 : ℝ) ^ q)))
      (u j) (δ j) B₀ (hδ j)
    convert! hsource j q hj using 1
    dsimp [B₀]
    ring
  obtain ⟨B, hB, hb⟩ := nonnegative_uniform_bound_of_eventually_le _ B₀ hbound
  exact ⟨B, hB, fun j => ⟨hI j, hb j⟩⟩

theorem source_unnormalized_second_moments_on_ball {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (u : ℕ → Ambient d → ℝ) (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j))
    (a : Ambient d) (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ)
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ M : ℝ, 0 ≤ M ∧ G * r ^ n ≤ M ∧ ∀ j,
      (∫ x in ball a r, u j x ^ 2 ∂μ j) ≤ M * δ j ^ 2 := by
  obtain ⟨B, hB, hb⟩ := source_normalized_second_moments_on_ball n G μ hg u K hu
    a δ hδ N hN D b hsource r hr
  refine ⟨max B (G * r ^ n), hB.trans (le_max_left _ _), le_max_right _ _, ?_⟩
  intro j
  have h := (hb j).2
  simp only [div_pow, integral_div] at h
  exact ((div_le_iff₀ (sq_pos_of_pos (hδ j))).mp h).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

end

end RieszRectifiability

end OAI
