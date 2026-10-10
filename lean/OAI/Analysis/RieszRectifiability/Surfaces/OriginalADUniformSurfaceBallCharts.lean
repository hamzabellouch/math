import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.OriginalADMatchedSurfaceModels
import OAI.Analysis.RieszRectifiability.Surfaces.SurfaceBallTransferFoundations

namespace OAI

/-!
# Uniform ball charts for active-region surfaces

Matched surface models give a precision independent of the support cell. For
each positive loss tolerance, a finite-depth ball chart covers the model up to
weighted Hausdorff area bounded by that tolerance times the original cell mass.
Its Lipschitz constant is chosen before the cell scale and center.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_original_AD_uniform_surface_ball_charts {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular n μ)
    (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 281474976710656 ∧ activeProjectionError d ε ≤ 1 / 128 ∧
      ∀ δ : ℝ, 0 < δ → ∃ M : ℝ≥0,
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
        AdmissibleRadius μ (latticeRadius R k / 8) →
        let Good := fun q : SupportCellDescendant μ R hR k z =>
          bilateralBeta n μ q.center (1024 * q.radius) < ε
        ∃ (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
          (hS : ∀ i, IsAffineNPlane n (S i)),
          (∀ i, activeRegionCell Good i → bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) ∧
          ∃ f : S (supportCellRoot μ R hR k z) → Ambient d,
            IsActiveRegionLimitModel μ R hR k z Good S hS ε f ∧
            ∃ g : ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
              LipschitzWith M g ∧ Set.range g ⊆ closedBall (z : Ambient d) (3 * latticeRadius R k) ∧
              (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
                (μH[(n : ℝ)] : Measure (Ambient d))
                  ((Set.range f ∩ closedBall (z : Ambient d) (3 * latticeRadius R k)) \ Set.range g) ≤
                    ENNReal.ofReal δ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨Ktop, hKtop, K, hK, hmodels⟩ := exists_original_AD_matched_surface_models hn hnd μ hAD
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨κ, hκ, hκquarter, σ, hσ, hwidth, hpair, hshadow⟩ := exists_projection_region_thresholds n K K hKpos hKpos
  obtain ⟨ε, hε, hεfine, hsmall, hprecision⟩ := exists_matched_surface_precision d σ hσ
  refine ⟨ε, hε, by linarith, by linarith, ?_⟩
  intro δ hδ
  obtain ⟨C, hC, hballs⟩ := hAD
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  let W := ENNReal.ofReal G + activeRegionStopMassAreaConstant n G
  have hW : W < ⊤ := by
    have hstop := activeRegionStopMassAreaConstant_lt_top n G
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hstop⟩
  have hθ := nativeCoreAreaFraction_pos_le_half n K hKpos
  have hzero : 0 ≤ 1 - nativeCoreAreaFraction n K := by linarith [hθ.2]
  have hone : 1 - nativeCoreAreaFraction n K < 1 := by linarith [hθ.1]
  obtain ⟨J, hJ⟩ := exists_depth_for_weighted_geometric_loss
    (1 - nativeCoreAreaFraction n K) hzero hone W hW (K * C * (64 : ℝ) ^ n) (by positivity) δ hδ
  let M := finiteBallChartUnionConstant d (11 ^ d) (projectionRegionDepthConstant d (Real.toNNReal (2 / κ)) J)
  refine ⟨M, ?_⟩
  intro R hR k z hcore
  let Good := fun q : SupportCellDescendant μ R hR k z =>
    bilateralBeta n μ q.center (1024 * q.radius) < ε
  obtain ⟨S, hS, hfit, f, hmodel, _, hreg, hs, _, hdiam, hgν, hlν, hplanes⟩ :=
    hmodels ε hε hεfine hsmall R hR k z hcore
  let ν := nativeSurfaceArea n (Set.range f)
  have hgeometry : ∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
      ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
        (∀ x ∈ ν.support ∩ closedBall p (1024 * r),
          infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ σ * r) ∧
        closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
          P.orthogonalProjectionOnto '' (ν.support ∩ closedBall p (r / 16)) := by
    intro p hp r hr
    obtain ⟨P, hP, hheight, hcover⟩ := hplanes p hp r hr
    exact ⟨P, hP, fun x hx => (hheight x hx).trans (mul_le_mul_of_nonneg_right hprecision hr.le), hcover⟩
  obtain ⟨g, hglip, hgrange, harea⟩ := exists_matched_surface_ball_depth_chart ν (Set.range f) rfl hs
    K K hKpos hKpos hgν (fun p hp r hr => hlν p hp r hr.1) σ κ hσ hκ (by linarith) hwidth hpair hshadow
    hgeometry hdiam hn J (latticeRadius R k) (latticeRadius_pos R hR k) z
  have hmass := radius_eight_growth_le_original_cell_mass μ C G hCpos hG hg
    (fun p hp r hr => (hballs p hp r hr).1) R hR k hcore z K hKpos.le
  refine ⟨S, hS, hfit, f, hmodel, g, hglip, hgrange, ?_⟩
  calc
    _ ≤ W * ((ENNReal.ofReal (1 - nativeCoreAreaFraction n K)) ^ J *
        (ENNReal.ofReal (K * C * (64 : ℝ) ^ n) * μ (cleanSupportCell μ R hR k z))) :=
      mul_le_mul' le_rfl (harea.trans (mul_le_mul' le_rfl hmass))
    _ = (W * (ENNReal.ofReal (1 - nativeCoreAreaFraction n K)) ^ J *
        ENNReal.ofReal (K * C * (64 : ℝ) ^ n)) * μ (cleanSupportCell μ R hR k z) := by ring
    _ ≤ _ := mul_le_mul' hJ le_rfl

end

end RieszRectifiability

end OAI
