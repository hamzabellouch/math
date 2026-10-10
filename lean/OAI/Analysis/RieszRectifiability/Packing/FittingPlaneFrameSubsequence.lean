import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.AffinePlaneNormalFrame
import OAI.Analysis.RieszRectifiability.Flatness.PlaneSupportFromMoments
import OAI.Analysis.RieszRectifiability.Packing.IsometricFrameCompactness

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem closest_plane_base_tendsto_zero {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, (S j : Set (Ambient d)).Nonempty)
    (a : ℕ → Ambient d) (ha : ∀ j, ‖a j‖ = infDist (0 : Ambient d) (S j : Set (Ambient d)))
    (hlim : Tendsto (fun j => ∫ x in ball (0 : Ambient d) 2,
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact Eventually.of_forall fun j => hr.trans_le (norm_nonneg (a j))
  · intro ε hε
    have hlim' : Tendsto (fun j => ∫ x in ball (0 : Ambient d) (1 + 1),
        infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0) := by
      simpa only [one_add_one_eq_two] using! hlim
    filter_upwards [moving_plane_support_tube_of_moments n μ C hC hlower hdiam
      S hS 0 1 hlim' ε hε] with j hj
    rw [ha j]
    exact hj 0 (mem_ball_self zero_lt_one) (hzero j)

theorem exists_fitting_plane_frame_subsequence {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane n (S j))
    (hlim : Tendsto (fun j => ∫ x in ball (0 : Ambient d) 2,
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ a : ℕ → Ambient d,
      ∃ L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - n) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient n →ₗᵢ[ℝ] Ambient d,
        Tendsto a atTop (𝓝 0) ∧
        Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
        (∀ j, a j ∈ S (ρ j)) ∧
        (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
        (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
        (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
          N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
        ∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
          ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖ := by
  choose a ha hnorm L hL N horth hsplit hdist using fun j =>
    exists_affine_plane_normal_frame (S j) (hS j)
  have ha0 := closest_plane_base_tendsto_zero μ C hC hlower hdiam hzero S
    (fun j => (hS j).1) a hnorm hlim
  obtain ⟨ρ, hρ, Llim, hLlim⟩ := exists_isometric_frame_subsequence L
  exact ⟨ρ, hρ, (fun j => a (ρ j)), (fun j => L (ρ j)), (fun j => N (ρ j)),
    Llim, ha0.comp hρ.tendsto_atTop, hLlim,
    (fun j => ha (ρ j)), (fun j => hL (ρ j)), (fun j => horth (ρ j)),
    (fun j => hsplit (ρ j)), (fun j => hdist (ρ j))⟩

end

end RieszRectifiability

end OAI
