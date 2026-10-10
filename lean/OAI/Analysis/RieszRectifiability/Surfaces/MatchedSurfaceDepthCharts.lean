import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.ProjectionRegionDepthCharts
import OAI.Analysis.RieszRectifiability.Projections.ContractingProjectionRegions

namespace OAI

/-!
# Matched surface charts with controlled loss

For surfaces of infinite support diameter, contracting projection regions provide
finite-depth charts with geometric mass loss. Choosing the depth from a positive
loss tolerance gives one Lipschitz bound valid at every lattice scale and cell.
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

theorem exists_matched_surface_depth_chart (J : ℕ) :
    ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets ν R hR k).points),
      ∃ g : ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
        LipschitzWith (projectionRegionDepthConstant d (Real.toNNReal (2 / κ)) J) g ∧
        Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
        ν (cleanSupportCell ν R hR k z \ Set.range g) ≤
          (ENNReal.ofReal (1 - nativeCoreAreaFraction n G)) ^ J * ν (cleanSupportCell ν R hR k z) := by
  have hL : 1 ≤ Real.toNNReal (2 / κ) := by
    have h : (1 : ℝ) ≤ (Real.toNNReal (2 / κ) : ℝ) := by
      rw [Real.coe_toNNReal _ (by positivity)]
      apply (le_div_iff₀ hκ).mpr
      linarith
    exact_mod_cast h
  apply exists_projection_region_depth_chart ν (Real.toNNReal (2 / κ)) hL (nativeCoreAreaFraction n G) ?_ J
  intro R hR k z
  have hcore : AdmissibleRadius ν (latticeRadius R k / 8) := by
    refine ⟨by have hr := latticeRadius_pos R hR k; positivity, ?_⟩
    rw [hdiam]
    exact le_top
  obtain ⟨Good, _, P, hdim, hsep, _, hstop⟩ := exists_contracting_projection_region
    ν A hν hsupport C G hC hG hg hlower σ κ hσ hκ hκ1 hwidth hsmall hshadow hgeometry R hR k hcore z
  refine ⟨Good, P, hdim, ?_, hstop⟩
  simpa only [Real.coe_toNNReal _ (by positivity : 0 ≤ 2 / κ)] using! hsep

theorem exists_matched_surface_uniform_small_loss_chart (δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℝ≥0, ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets ν R hR k).points),
      ∃ g : ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
        LipschitzWith M g ∧
        Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
        ν (cleanSupportCell ν R hR k z \ Set.range g) ≤
          ENNReal.ofReal δ * ν (cleanSupportCell ν R hR k z) := by
  have hθ := nativeCoreAreaFraction_pos_le_half n G hG
  have hzero : 0 ≤ 1 - nativeCoreAreaFraction n G := by linarith [hθ.2]
  have hone : 1 - nativeCoreAreaFraction n G < 1 := by linarith [hθ.1]
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hzero hone
  have hevent : ∀ᶠ J : ℕ in atTop, (1 - nativeCoreAreaFraction n G) ^ J < δ :=
    hlim.eventually (gt_mem_nhds hδ)
  obtain ⟨J, hJ⟩ := hevent.exists
  refine ⟨projectionRegionDepthConstant d (Real.toNNReal (2 / κ)) J, ?_⟩
  intro R hR k z
  obtain ⟨g, hg, hrange, hdeficit⟩ := exists_matched_surface_depth_chart
    ν A hν hsupport C G hC hG hg hlower σ κ hσ hκ hκ1 hwidth hsmall hshadow hgeometry hdiam J R hR k z
  refine ⟨g, hg, hrange, hdeficit.trans (mul_le_mul' ?_ le_rfl)⟩
  rw [← ENNReal.ofReal_pow hzero]
  exact ENNReal.ofReal_le_ofReal hJ.le

end

end RieszRectifiability

end OAI
