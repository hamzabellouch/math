import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.OriginalADActiveRegionAllRadiusAreaModel

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ENNReal

theorem exists_actual_AD_uniform_precision_area_models {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular n μ) :
    ∃ Ktop : ℝ≥0∞, Ktop < ⊤ ∧ ∃ Kupper : ℝ≥0∞, Kupper < ⊤ ∧
      ∃ Klower : ℝ≥0∞, 0 < Klower ∧ Klower < ⊤ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 281474976710656 → activeProjectionError d ε ≤ 1 / 128 →
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
  by_cases hsupport : μ.support.Nontrivial
  · obtain ⟨G, hg⟩ := globalGrowth_of_ADRegular_nontrivial n μ hAD hsupport
    have hG : 0 < G + 1 := by linarith [hg.1]
    have hg' : GlobalUpperGrowth n (G + 1) μ := hg.mono_constant (by linarith)
    obtain ⟨C, hC, hballs⟩ := hAD
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    refine ⟨activeRegionUniformAreaConstant n d C (G + 1),
      activeRegionUniformAreaConstant_lt_top n d C (G + 1),
      activeRegionLocalUpperAreaConstant n d C (G + 1),
      activeRegionLocalUpperAreaConstant_lt_top n d C (G + 1),
      activeRegionAllRadiusLowerAreaConstant n C (G + 1),
      activeRegionAllRadiusLowerAreaConstant_pos n C (G + 1),
      activeRegionAllRadiusLowerAreaConstant_lt_top n C (G + 1), ?_⟩
    intro ε hε hεfine hsmall R hR k z hcore
    let Good := fun q : SupportCellDescendant μ R hR k z =>
      bilateralBeta n μ q.center (1024 * q.radius) < ε
    have hεtiny : ε ≤ 1 / 268435456 := by linarith
    obtain ⟨S, hS, hfit, _⟩ := exists_active_level_projection_maps μ R hR k z hnd ε hε
    obtain ⟨f, hmodel⟩ := exists_active_region_limit_model μ R hR k z Good S hS ε hε hεtiny hsmall hfit
    refine ⟨S, hS, hfit, f, hmodel,
      active_region_limit_isClosedEmbedding μ R hR k z Good S hS ε hε hεtiny hsmall hfit f hmodel,
      active_region_limit_area_le_original_top μ C (G + 1) hCpos hG hg'
        (fun x hx r hr => (hballs x hx r hr).1) R hR k hcore z Good S hS ε hε hεfine hsmall hfit f hmodel,
      ?_, ?_⟩
    · intro p r hr
      exact active_region_limit_local_ball_area_le μ C (G + 1) hCpos hG hg'
        (fun x hx s hs => (hballs x hx s hs).1) R hR k hcore z Good S hS
        ε hε hεfine hsmall hfit f hmodel p r hr
    · intro p hp r hr
      exact active_region_limit_all_radius_ball_area_ge hn μ C (G + 1) hCpos hG hg'
        (fun x hx s hs => (hballs x hx s hs).1) R hR k hcore z Good S hS
        ε hε hεfine hsmall hfit f hmodel p hp r hr
  · refine ⟨0, by norm_num, 0, by norm_num, 1, by norm_num, by norm_num, ?_⟩
    intro ε hε hεfine hsmall R hR k z hcore
    have hdiam : ediam μ.support = 0 := ediam_eq_zero_iff.mpr (Set.not_nontrivial_iff.mp hsupport)
    have hzero : ENNReal.ofReal (latticeRadius R k / 8) = 0 :=
      le_antisymm (hdiam ▸ hcore.2) (zero_le)
    exact ((ENNReal.ofReal_pos.mpr hcore.1).ne' hzero).elim

end

end RieszRectifiability

end OAI
