import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.OriginalADActiveRegionContractibleAreaModel
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLocalUpperArea

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ENNReal

theorem exists_actual_AD_active_region_local_upper_area_models {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular n μ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 281474976710656 ∧ activeProjectionError d ε ≤ 1 / 128 ∧
      ∃ Ktop : ℝ≥0∞, Ktop < ⊤ ∧ ∃ Klocal : ℝ≥0∞, Klocal < ⊤ ∧
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
            ∀ (p : Ambient d) (r : ℝ), 0 < r →
              (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) ≤
                Klocal * (ENNReal.ofReal r) ^ n := by
  obtain ⟨ε, hε, hεfine, hsmall, Ktop, hKtop, hmodels⟩ :=
    exists_actual_AD_active_region_contractible_area_models hnd μ hAD
  refine ⟨ε, hε, hεfine, hsmall, Ktop, hKtop, ?_⟩
  by_cases hsupport : μ.support.Nontrivial
  · obtain ⟨G, hg⟩ := globalGrowth_of_ADRegular_nontrivial n μ hAD hsupport
    have hG : 0 < G + 1 := by linarith [hg.1]
    have hg' : GlobalUpperGrowth n (G + 1) μ := hg.mono_constant (by linarith)
    obtain ⟨C, hC, hballs⟩ := hAD
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    refine ⟨activeRegionLocalUpperAreaConstant n d C (G + 1),
      activeRegionLocalUpperAreaConstant_lt_top n d C (G + 1), ?_⟩
    intro R hR k z hcore
    let Good := fun q : SupportCellDescendant μ R hR k z =>
      bilateralBeta n μ q.center (1024 * q.radius) < ε
    obtain ⟨S, hS, hfit, f, hmodel, hembed, hcontract, htop⟩ := hmodels R hR k z hcore
    refine ⟨S, hS, hfit, f, hmodel, hembed, hcontract, htop, ?_⟩
    intro p r hr
    exact active_region_limit_local_ball_area_le μ C (G + 1) hCpos hG hg'
      (fun x hx s hs => (hballs x hx s hs).1) R hR k hcore z Good S hS
      ε hε hεfine hsmall hfit f hmodel p r hr
  · refine ⟨0, by norm_num, ?_⟩
    intro R hR k z hcore
    have hdiam : ediam μ.support = 0 := ediam_eq_zero_iff.mpr (Set.not_nontrivial_iff.mp hsupport)
    have hzero : ENNReal.ofReal (latticeRadius R k / 8) = 0 :=
      le_antisymm (hdiam ▸ hcore.2) (zero_le)
    exact ((ENNReal.ofReal_pos.mpr hcore.1).ne' hzero).elim

end

end RieszRectifiability

end OAI
