import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.MatchedSurfaceDepthCharts
import OAI.Analysis.RieszRectifiability.Surfaces.SurfaceBallChartAssembly

namespace OAI

/-!
# Finite-depth charts on surface balls

Finite unions of matched-surface cell charts produce maps from Euclidean balls.
The construction retains the finite-depth mass-deficit estimate and an explicit
Lipschitz bound determined by the cell-chart bound and the covering multiplicity.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

variable {n d : ℕ}
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (σ κ : ℝ) (hσ : 0 < σ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hwidth : σ + κ ≤ 1) (hsmall : 2048 * σ * (κ + 1) ≤ κ)
    (hshadow : projectionStopShadowConstant n C σ κ ≤ nativeCoreAreaFraction n G)
    (hgeometry : ∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
      ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
        (∀ x ∈ ν.support ∩ closedBall p (1024 * r),
          infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ σ * r) ∧
        closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
          P.orthogonalProjectionOnto '' (ν.support ∩ closedBall p (r / 16)))
    (hdiam : ediam ν.support = ⊤)

include hν hsupport hC hG hg hlower hσ hκ hκ1 hwidth hsmall hshadow hgeometry hdiam

theorem exists_matched_surface_ball_depth_chart (hn : 0 < n) (J : ℕ)
    (r : ℝ) (hr : 0 < r) (a : Ambient d) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (finiteBallChartUnionConstant d (11 ^ d)
        (projectionRegionDepthConstant d (Real.toNNReal (2 / κ)) J)) g ∧
      Set.range g ⊆ closedBall a (3 * r) ∧
      (μH[(n : ℝ)] : Measure (Ambient d)) ((A ∩ closedBall a (3 * r)) \ Set.range g) ≤
        (ENNReal.ofReal (1 - nativeCoreAreaFraction n G)) ^ J * ENNReal.ofReal (G * (8 * r) ^ n) := by
  apply exists_surface_ball_chart_of_cell_deficits hn ν A hν hsupport C G hC hG hg hlower
    r hr a (projectionRegionDepthConstant d (Real.toNNReal (2 / κ)) J)
    ((ENNReal.ofReal (1 - nativeCoreAreaFraction n G)) ^ J)
  intro z
  have hlocal := exists_matched_surface_depth_chart ν A hν hsupport C G hC hG hg hlower
    σ κ hσ hκ hκ1 hwidth hsmall hshadow hgeometry hdiam J r hr 0 z.val
  obtain ⟨g₀, hg₀, _, hdef⟩ := hlocal
  let cast : ball (0 : Ambient n) r → ball (0 : Ambient n) (latticeRadius r 0) :=
    fun u => ⟨u.val, by simpa only [latticeRadius_zero] using! u.property⟩
  have hcast : Isometry cast := fun _ _ => rfl
  have hsurj : Function.Surjective cast := by
    intro u
    exact ⟨⟨u.val, by simpa only [latticeRadius_zero] using! u.property⟩, Subtype.ext rfl⟩
  let g := g₀ ∘ cast
  have hrange : Set.range g = Set.range g₀ := by
    apply Set.Subset.antisymm
    · rintro y ⟨u, rfl⟩
      exact Set.mem_range_self (cast u)
    · rintro y ⟨u, rfl⟩
      obtain ⟨v, hv⟩ := hsurj u
      exact ⟨v, congrArg g₀ hv⟩
  refine ⟨g, ?_, ?_⟩
  · simpa only [mul_one] using! hg₀.comp hcast.lipschitzWith
  · rw [hrange]
    exact hdef

end

end RieszRectifiability

end OAI
