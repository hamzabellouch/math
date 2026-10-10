import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitOrigin
import OAI.Analysis.RieszRectifiability.Limits.OriginalADLimit
import OAI.Analysis.RieszRectifiability.Kernel.DyadicMomentAllRadii
import OAI.Analysis.RieszRectifiability.Limits.MovingTubeSupportLimit
import OAI.Analysis.RieszRectifiability.Foundations.BoundedPlanarDensity

namespace OAI

/-!
# Dyadic planar measure limits

Vanishing dyadic plane moments yield a subsequential AD growth limit supported on a
linear plane through the origin. The limit has a bounded intrinsic density, while
the convergent frames retain the normal-coordinate moment and local `MemLp` bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_planar_measure_limit {n d : ℕ}
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
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      ∃ a : ℕ → Ambient d, ∃ L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - n) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient n →ₗᵢ[ℝ] Ambient d,
        IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        CompactTestConvergence (fun j => μ (ρ j)) ν ∧ GlobalUpperGrowth n (G * 2 ^ n) ν ∧
        (∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
          ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r)) ∧
        ν.support ⊆ (Llim.toLinearMap.range : Set (Ambient d)) ∧
        (0 : Ambient d) ∈ ν.support ∧
        (∃ f : Ambient n → ℝ, Measurable f ∧
          (∀ x, 0 ≤ f x ∧ f x ≤ intrinsicGrowthDensityBound n (G * 2 ^ n)) ∧
          ((volume : Measure (Ambient n)).withDensity (fun x => ENNReal.ofReal (f x))).map Llim = ν) ∧
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
  obtain ⟨α, hα, a, L, N, Llim, ha0, hLlim, ha, hL, horth, hsplit, hdist, hmem, hsource⟩ :=
    exists_dyadically_controlled_frame_subsequence μ C G hC hg hlower hdiam hzero
      S hS δ T hδ hT M b hmoment
  obtain ⟨β, hβ, ν, hfinite, hne, hlocal, hgν, hlowerν⟩ := exists_original_AD_growth_limit n
    (fun j => μ (α j)) C G hC (fun j => hg (α j)) (fun j => hlower (α j))
      (fun r hr => hα.tendsto_atTop.eventually (hdiam r hr)) (fun j => hzero (α j))
  let := hfinite
  have hρ : StrictMono (fun j => α (β j)) := hα.comp hβ
  have hsupport : ν.support ⊆ (Llim.toLinearMap.range : Set (Ambient d)) := by
    apply moving_plane_limit_support (fun j => μ (α (β j))) ν hlocal C hC
      (fun j => hlower (α (β j))) (fun r hr => hρ.tendsto_atTop.eventually (hdiam r hr))
      (fun j => S (α (β j))) (fun j => (hS (α (β j))).1)
      (fun j => a (β j)) (fun j => ha (β j)) (ha0.comp hβ.tendsto_atTop)
      (fun j => L (β j)) (fun j => hL (β j)) Llim (hLlim.comp hβ.tendsto_atTop)
    intro R _hR
    exact (fixed_plane_moment_tendsto_zero_on_ball μ S (fun j => (hS j).1)
      δ T hδ hT M b hmoment R).comp hρ.tendsto_atTop
  have horigin : (0 : Ambient d) ∈ ν.support := compactTestConvergence_origin_mem_support n
    (fun j => μ (α (β j))) ν hlocal C hC (fun j => hlower (α (β j)))
      (fun r hr => hρ.tendsto_atTop.eventually (hdiam r hr)) (fun j => hzero (α (β j)))
  have hdensity := exists_bounded_planar_density Llim ν hsupport (G * 2 ^ n) hgν
  refine ⟨(fun j => α (β j)), hρ, ν, (fun j => a (β j)), (fun j => L (β j)),
    (fun j => N (β j)), Llim, hfinite, hne, hlocal, hgν, hlowerν, hsupport, horigin, hdensity,
    ha0.comp hβ.tendsto_atTop, hLlim.comp hβ.tendsto_atTop,
    (fun j => ha (β j)), (fun j => hL (β j)), (fun j => horth (β j)),
    (fun j => hsplit (β j)), (fun j => hdist (β j)), ?_, ?_⟩
  · exact fun i j R hR => hmem i (β j) R hR
  · exact fun i j l hl => hsource i (β j) l hl

end

end RieszRectifiability

end OAI
