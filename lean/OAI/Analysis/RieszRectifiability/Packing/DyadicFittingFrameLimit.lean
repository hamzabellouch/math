import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.NormalHeightFromPlaneMoments
import OAI.Analysis.RieszRectifiability.Packing.FittingPlaneFrameSubsequence

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem fixed_plane_dyadic_moment_tendsto_zero {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (S : ℕ → AffineSubspace ℝ (Ambient d))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2)) (l : ℕ) :
    Tendsto (fun j => ∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l),
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0) := by
  have hlim : Tendsto (fun j => M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2)) atTop (𝓝 0) := by
    simpa using! (((hδ.mul_const (b ^ l)).pow 2).const_mul M).mul_const (((2 : ℝ) ^ l) ^ (n + 2))
  apply squeeze_zero' (Eventually.of_forall (fun j =>
    integral_nonneg (fun x => sq_nonneg (infDist x (S j : Set (Ambient d)))))) _ hlim
  filter_upwards [hT.eventually (eventually_ge_atTop l)] with j hj
  exact hmoment j l hj

theorem exists_dyadically_controlled_frame_subsequence {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane n (S j))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ a : ℕ → Ambient d,
      ∃ L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - n) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient n →ₗᵢ[ℝ] Ambient d,
        Tendsto a atTop (𝓝 0) ∧
        Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
        (∀ j, a j ∈ S (ρ j)) ∧ (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
        (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
        (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
          N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
        (∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
          ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖) ∧
        (∀ i : Fin (d - n), ∀ j : ℕ, ∀ R : ℝ, 0 < R →
          MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
            ((μ (ρ j)).restrict (ball 0 R))) ∧
        ∀ i : Fin (d - n), ∀ j l, l ≤ T (ρ j) →
          (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), normalCoordinate (a j) (N j) i x ^ 2 ∂μ (ρ j)) ≤
            δ (ρ j) ^ 2 * M * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2 := by
  have hlim : Tendsto (fun j => ∫ x in ball (0 : Ambient d) 2,
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0) := by
    simpa only [pow_one] using! fixed_plane_dyadic_moment_tendsto_zero μ S δ T hδ hT M b hmoment 1
  obtain ⟨ρ, hρ, a, L, N, Llim, ha0, hLlim, ha, hL, horth, hsplit, hdist⟩ :=
    exists_fitting_plane_frame_subsequence μ C hC hlower hdiam hzero S hS hlim
  refine ⟨ρ, hρ, a, L, N, Llim, ha0, hLlim, ha, hL, horth, hsplit, hdist, ?_, ?_⟩
  · intro i j R hR
    exact normalized_normalCoordinate_memLp_on_ball n (μ (ρ j)) G (hg (ρ j))
      (a j) (N j) i R hR (δ (ρ j))
  · intro i j l hl
    exact normalCoordinate_dyadic_source_bound (μ (ρ j)) G (hg (ρ j))
      (S (ρ j)) (hS (ρ j)).1 (a j) (N j) (hdist j) M (δ (ρ j)) b l (hmoment (ρ j) l hl) i

end

end RieszRectifiability

end OAI
