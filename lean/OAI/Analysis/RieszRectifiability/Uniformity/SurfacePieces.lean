import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionUniformArea
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLocalUpperArea
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionAllRadiusLowerArea
import OAI.Analysis.RieszRectifiability.Surfaces.ActualNativeSurfaceGeometry
import OAI.Analysis.RieszRectifiability.Surfaces.MatchedSurfacePrecision
import OAI.Analysis.RieszRectifiability.Surfaces.MatchedSurfaceBallDepthCharts
import OAI.Analysis.RieszRectifiability.Surfaces.SurfaceBallOriginalMass
import OAI.Analysis.RieszRectifiability.Restart.SelectedRestartBallChartData

namespace OAI

/-!
# Class-uniform surface pieces for restart charts

Uniform upper and lower area estimates give native surface measures with common
growth and projection bounds. A geometric loss estimate then chooses a finite
chart depth for any positive deficit. The precision, Lipschitz bounds, and restart
piece parameters are selected from the fixed dimensions and regularity constants
before the original measure or its support cell is introduced.
-/

namespace RieszRectifiability
noncomputable section
open MeasureTheory Metric Set Topology
open scoped NNReal ENNReal

/-- Area comparison constants are uniform over the measure class and the allowed precision. -/
theorem quantitative_uniform_precision_area_models {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    (C G : ℝ) (hC : 1 ≤ C) (hG : 0 < G) :
    ∃ Ktop : ℝ≥0∞, Ktop < ⊤ ∧ ∃ Kupper : ℝ≥0∞, Kupper < ⊤ ∧
      ∃ Klower : ℝ≥0∞, 0 < Klower ∧ Klower < ⊤ ∧
      ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant n C μ →
      GlobalUpperGrowth n G μ → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 281474976710656 → activeProjectionError d ε ≤ 1 / 128 →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
        AdmissibleRadius μ (latticeRadius R k / 8) →
        let Good := fun q : SupportCellDescendant μ R hR k z =>
          bilateralBeta n μ q.center (1024 * q.radius) < ε
        ∃ (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
          (hS : ∀ i, IsAffineNPlane n (S i)),
          (∀ i, activeRegionCell Good i → bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) ∧
          ∃ f : S (supportCellRoot μ R hR k z) → Ambient d,
            IsActiveRegionLimitModel μ R hR k z Good S hS ε f ∧ IsClosedEmbedding f ∧
            (μH[(n : ℝ)] : Measure (Ambient d))
              (Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k)) ≤
                Ktop * μ (cleanSupportCell μ R hR k z) ∧
            (∀ (p : Ambient d) (r : ℝ), 0 < r →
              (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) ≤
                Kupper * (ENNReal.ofReal r) ^ n) ∧
            ∀ p ∈ Set.range f, ∀ (r : ℝ), 0 < r →
              Klower * (ENNReal.ofReal r) ^ n ≤
                (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  refine ⟨activeRegionUniformAreaConstant n d C G,
    activeRegionUniformAreaConstant_lt_top n d C G,
    activeRegionLocalUpperAreaConstant n d C G,
    activeRegionLocalUpperAreaConstant_lt_top n d C G,
    activeRegionAllRadiusLowerAreaConstant n C G,
    activeRegionAllRadiusLowerAreaConstant_pos n C G,
    activeRegionAllRadiusLowerAreaConstant_lt_top n C G, ?_⟩
  intro μ _hreg hAD hg ε hε hεfine hsmall R hR k z hcore
  have hballs := hAD.2
  let Good := fun q : SupportCellDescendant μ R hR k z =>
    bilateralBeta n μ q.center (1024 * q.radius) < ε
  have hεtiny : ε ≤ 1 / 268435456 := by linarith
  obtain ⟨S, hS, hfit, _⟩ := exists_active_level_projection_maps μ R hR k z hnd ε hε
  obtain ⟨f, hmodel⟩ := exists_active_region_limit_model μ R hR k z Good S hS ε hε hεtiny hsmall hfit
  refine ⟨S, hS, hfit, f, hmodel,
    active_region_limit_isClosedEmbedding μ R hR k z Good S hS ε hε hεtiny hsmall hfit f hmodel,
    active_region_limit_area_le_original_top μ C G hCpos hG hg
      (fun x hx r hr => (hballs x hx r hr).1) R hR k hcore z Good S hS ε hε hεfine hsmall hfit f hmodel,
    ?_, ?_⟩
  · intro p r hr
    exact active_region_limit_local_ball_area_le μ C G hCpos hG hg
      (fun x hx s hs => (hballs x hx s hs).1) R hR k hcore z Good S hS
      ε hε hεfine hsmall hfit f hmodel p r hr
  · intro p hp r hr
    exact active_region_limit_all_radius_ball_area_ge hn μ C G hCpos hG hg
      (fun x hx s hs => (hballs x hx s hs).1) R hR k hcore z Good S hS
      ε hε hεfine hsmall hfit f hmodel p hp r hr

/-- The model surfaces carry regular, unbounded AD measures with common projection geometry. -/
theorem quantitative_matched_surface_models {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    (C₀ G : ℝ) (hC₀ : 1 ≤ C₀) (hG : 0 < G) :
    ∃ Ktop : ℝ≥0∞, Ktop < ⊤ ∧ ∃ K : ℝ, 1 ≤ K ∧
      ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant n C₀ μ →
      GlobalUpperGrowth n G μ → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 72057594037927936 → activeProjectionError d ε ≤ 1 / 4096 →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
        AdmissibleRadius μ (latticeRadius R k / 8) →
        let Good := fun q : SupportCellDescendant μ R hR k z =>
          bilateralBeta n μ q.center (1024 * q.radius) < ε
        ∃ (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
          (hS : ∀ i, IsAffineNPlane n (S i)),
          (∀ i, activeRegionCell Good i → bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) ∧
          ∃ f : S (supportCellRoot μ R hR k z) → Ambient d,
            IsActiveRegionLimitModel μ R hR k z Good S hS ε f ∧
            (μH[(n : ℝ)] : Measure (Ambient d))
              (Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k)) ≤
                Ktop * μ (cleanSupportCell μ R hR k z) ∧
            let ν := nativeSurfaceArea n (Set.range f)
            ν.Regular ∧ ν.support = Set.range f ∧ ADRegular n ν ∧ ediam ν.support = ⊤ ∧
              GlobalUpperGrowth n K ν ∧
              (∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
                ENNReal.ofReal (r ^ n / K) ≤ ν (ball p r)) ∧
              ∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
                ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
                  (∀ x ∈ ν.support ∩ closedBall p (1024 * r),
                    infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤
                      (281474976710656 * (ε + activeProjectionError d ε)) * r) ∧
                  closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
                    P.orthogonalProjectionOnto '' (ν.support ∩ closedBall p (r / 16)) := by
  obtain ⟨Ktop, hKtop, C, hC, c, hc, hcfin, hmodels⟩ :=
    quantitative_uniform_precision_area_models hn hnd C₀ G hC₀ hG
  have hK1 : 1 ≤ nativeSurfaceADConstant n c C := by
    have hCnonneg : 0 ≤ C.toReal := ENNReal.toReal_nonneg
    have hinv : 0 ≤ (c * (ENNReal.ofReal (1 / 2 : ℝ)) ^ n).toReal⁻¹ :=
      inv_nonneg.mpr ENNReal.toReal_nonneg
    dsimp only [nativeSurfaceADConstant]
    linarith
  refine ⟨Ktop, hKtop, nativeSurfaceADConstant n c C, hK1, ?_⟩
  intro μ _hreg hAD hg ε hε hεfine hsmall R hR k z hcore
  let Good := fun q : SupportCellDescendant μ R hR k z =>
    bilateralBeta n μ q.center (1024 * q.radius) < ε
  obtain ⟨S, hS, hfit, f, hmodel, hembed, htop, hupper, hlower⟩ :=
    hmodels μ hAD hg ε hε (by linarith) (by linarith) R hR k z hcore
  obtain ⟨hreg, hs, hADν, hdiam, _, hg, hl, hplanes⟩ :=
    active_region_native_surface_geometry hn μ R hR k z Good S hS ε hε hεfine hsmall hfit
      f hmodel hembed c C hc hcfin hC hlower hupper
  exact ⟨S, hS, hfit, f, hmodel, htop, hreg, hs, hADν, hdiam, hg, hl, hplanes⟩

/-- A measure-independent precision admits ball charts with any prescribed positive area deficit.
The Lipschitz constant may depend on that deficit, but is chosen before the measure. -/
theorem quantitative_uniform_surface_ball_charts {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    (C G : ℝ) (hC : 1 ≤ C) (hG : 0 < G) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 281474976710656 ∧ activeProjectionError d ε ≤ 1 / 128 ∧
      ∀ δ : ℝ, 0 < δ → ∃ M : ℝ≥0,
      ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant n C μ →
      GlobalUpperGrowth n G μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
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
  obtain ⟨Ktop, hKtop, K, hK, hmodels⟩ := quantitative_matched_surface_models hn hnd C G hC hG
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨κ, hκ, hκquarter, σ, hσ, hwidth, hpair, hshadow⟩ := exists_projection_region_thresholds n K K hKpos hKpos
  obtain ⟨ε, hε, hεfine, hsmall, hprecision⟩ := exists_matched_surface_precision d σ hσ
  refine ⟨ε, hε, by linarith, by linarith, ?_⟩
  intro δ hδ
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
  intro μ _hreg hAD hg R hR k z hcore
  have hballs := hAD.2
  let Good := fun q : SupportCellDescendant μ R hR k z =>
    bilateralBeta n μ q.center (1024 * q.radius) < ε
  obtain ⟨S, hS, hfit, f, hmodel, _, hreg, hs, _, hdiam, hgν, hlν, hplanes⟩ :=
    hmodels μ hAD hg ε hε hεfine hsmall R hR k z hcore
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

/-- Choose common piece-count and Lipschitz parameters before assembling all selected restarts. -/
theorem quantitative_uniform_restart_surface_pieces {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    (C G : ℝ) (hC : 1 ≤ C) (hG : 0 < G) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 281474976710656 ∧ activeProjectionError d ε ≤ 1 / 128 ∧
      ∀ δ : ℝ, 0 < δ → ∃ (N : ℕ) (P : ℝ≥0),
    ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant n C μ →
    GlobalUpperGrowth n G μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      let Bad := fun i : SupportCellDescendant μ R hR k z =>
        ε ≤ bilateralBeta n μ i.center (1024 * i.radius)
      ∃ (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
        (data : ∀ q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q},
          ¬ Bad q.val → SelectedRestartSurfaceData n Bad q.val (E q) ε N P),
        ∀ q hq, (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
          (μH[(n : ℝ)] : Measure (Ambient d))
            ((Set.range (data q hq).model ∩ closedBall q.val.center (3 * q.val.radius)) \ E q) ≤
              ENNReal.ofReal δ * μ q.val.cell := by
  classical
  obtain ⟨ε, hε, hεfine, hsmall, hcharts⟩ := quantitative_uniform_surface_ball_charts hn hnd C G hC hG
  refine ⟨ε, hε, hεfine, hsmall, ?_⟩
  intro δ hδ
  obtain ⟨M, hM⟩ := hcharts δ hδ
  refine ⟨1, M, ?_⟩
  intro μ _hreg hAD hg R hR k z hcore
  have hM := hM μ hAD hg
  let Bad := fun i : SupportCellDescendant μ R hR k z =>
    ε ≤ bilateralBeta n μ i.center (1024 * i.radius)
  let Q := {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}
  have hlocal (q : Q) :
      ∃ (S : SupportCellDescendant μ R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩ →
          AffineSubspace ℝ (Ambient d)) (hS : ∀ i, IsAffineNPlane n (S i)),
        (∀ i, activeRegionCell (relativeRestartGood Bad q.val) i →
          bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) ∧
        ∃ f : S (supportCellRoot μ R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩) → Ambient d,
          IsActiveRegionLimitModel μ R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩
            (relativeRestartGood Bad q.val) S hS ε f ∧
          ∃ g : ball (0 : Ambient n) q.val.radius → Ambient d,
            LipschitzWith M g ∧ Set.range g ⊆ closedBall q.val.center (3 * q.val.radius) ∧
            (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
              (μH[(n : ℝ)] : Measure (Ambient d))
                ((Set.range f ∩ closedBall q.val.center (3 * q.val.radius)) \ Set.range g) ≤
                  ENNReal.ofReal δ * μ q.val.cell := by
    have hqcore : AdmissibleRadius μ (latticeRadius R (k + q.val.depth) / 8) := by
      simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using! q.val.core_admissible hcore
    obtain ⟨S, hS, hfit, f, hmodel, g, hglip, hgrange, hloss⟩ :=
      hM R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩ hqcore
    have hGood : relativeRestartGood Bad q.val =
        (fun i => bilateralBeta n μ i.center (1024 * i.radius) < ε) := relativeRestartGood_beta_eq ε q.val
    exact ⟨S, hS, by simpa only [hGood] using! hfit,
      f, by simpa only [hGood] using! hmodel, g, hglip, hgrange, hloss⟩
  choose S hS hfit f hmodel g hglip hgrange hloss using hlocal
  let E (q : Q) : Set (Ambient d) := Set.range (g q)
  let data (q : Q) : SelectedRestartSurfaceData n Bad q.val (E q) ε 1 M :=
    selectedRestartSurfaceDataOfBallChart Bad q.val (S q) (hS q) ε (hfit q)
      (f q) (hmodel q) (g q) M (hglip q) (hgrange q)
  refine ⟨E, (fun q _ => data q), ?_⟩
  intro q _hq
  change (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
    (μH[(n : ℝ)] : Measure (Ambient d))
      ((Set.range (f q) ∩ closedBall q.val.center (3 * q.val.radius)) \ Set.range (g q)) ≤
        ENNReal.ofReal δ * μ q.val.cell
  exact hloss q

end
end RieszRectifiability

end OAI
