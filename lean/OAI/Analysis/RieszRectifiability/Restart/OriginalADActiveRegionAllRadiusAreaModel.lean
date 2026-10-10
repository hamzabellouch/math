import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.OriginalADActiveRegionLocalUpperAreaModel
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionAllRadiusLowerArea

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ENNReal

theorem exists_actual_AD_active_region_all_radius_area_models {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular n μ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 281474976710656 ∧ activeProjectionError d ε ≤ 1 / 128 ∧
      ∃ Ktop : ℝ≥0∞, Ktop < ⊤ ∧ ∃ Kupper : ℝ≥0∞, Kupper < ⊤ ∧
      ∃ Klower : ℝ≥0∞, 0 < Klower ∧ Klower < ⊤ ∧
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
        AdmissibleRadius μ (latticeRadius R k / 8) →
        let Good := fun q : SupportCellDescendant μ R hR k z =>
          bilateralBeta n μ q.center (1024 * q.radius) < ε
        ∃ (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
          (hS : ∀ i, IsAffineNPlane n (S i)),
          (∀ i, activeRegionCell Good i → bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) ∧
          ∃ f : S (supportCellRoot μ R hR k z) → Ambient d,
            IsActiveRegionLimitModel μ R hR k z Good S hS ε f ∧ IsClosedEmbedding f ∧
            HasBoundedBallContractions (Set.range f) 50331648 ∧
            (μH[(n : ℝ)] : Measure (Ambient d))
              (Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k)) ≤
                Ktop * μ (cleanSupportCell μ R hR k z) ∧
            (∀ (p : Ambient d) (r : ℝ), 0 < r →
              (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) ≤
                Kupper * (ENNReal.ofReal r) ^ n) ∧
            ∀ p ∈ Set.range f, ∀ (r : ℝ), 0 < r →
              Klower * (ENNReal.ofReal r) ^ n ≤
                (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  obtain ⟨ε, hε, hεfine, hsmall, Ktop, hKtop, Kupper, hKupper, hmodels⟩ :=
    exists_actual_AD_active_region_local_upper_area_models hnd μ hAD
  refine ⟨ε, hε, hεfine, hsmall, Ktop, hKtop, Kupper, hKupper, ?_⟩
  by_cases hsupport : μ.support.Nontrivial
  · obtain ⟨G, hg⟩ := globalGrowth_of_ADRegular_nontrivial n μ hAD hsupport
    have hG : 0 < G + 1 := by linarith [hg.1]
    have hg' : GlobalUpperGrowth n (G + 1) μ := hg.mono_constant (by linarith)
    obtain ⟨C, hC, hballs⟩ := hAD
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    refine ⟨activeRegionAllRadiusLowerAreaConstant n C (G + 1),
      activeRegionAllRadiusLowerAreaConstant_pos n C (G + 1),
      activeRegionAllRadiusLowerAreaConstant_lt_top n C (G + 1), ?_⟩
    intro R hR k z hcore
    let Good := fun q : SupportCellDescendant μ R hR k z =>
      bilateralBeta n μ q.center (1024 * q.radius) < ε
    obtain ⟨S, hS, hfit, f, hmodel, hembed, hcontract, htop, hupper⟩ := hmodels R hR k z hcore
    refine ⟨S, hS, hfit, f, hmodel, hembed, hcontract, htop, hupper, ?_⟩
    intro p hp r hr
    exact active_region_limit_all_radius_ball_area_ge hn μ C (G + 1) hCpos hG hg'
      (fun x hx s hs => (hballs x hx s hs).1) R hR k hcore z Good S hS
      ε hε hεfine hsmall hfit f hmodel p hp r hr
  · refine ⟨1, by norm_num, by norm_num, ?_⟩
    intro R hR k z hcore
    have hdiam : ediam μ.support = 0 := ediam_eq_zero_iff.mpr (Set.not_nontrivial_iff.mp hsupport)
    have hzero : ENNReal.ofReal (latticeRadius R k / 8) = 0 :=
      le_antisymm (hdiam ▸ hcore.2) (zero_le)
    exact ((ENNReal.ofReal_pos.mpr hcore.1).ne' hzero).elim

end

end RieszRectifiability

end OAI
