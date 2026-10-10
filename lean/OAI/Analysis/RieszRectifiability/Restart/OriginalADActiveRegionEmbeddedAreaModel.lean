import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.OriginalADActiveRegionAreaModel
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLimitEmbedding

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ENNReal

theorem exists_actual_AD_active_region_embedded_area_models {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular n μ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 281474976710656 ∧ activeProjectionError d ε ≤ 1 / 128 ∧
      ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
        (z : (supportLatticeNets μ R hR k).points),
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
                K * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨ε, hε, hεfine, hsmall, K, hK, hmodels⟩ :=
    exists_actual_AD_active_region_area_models hnd μ hAD
  refine ⟨ε, hε, hεfine, hsmall, K, hK, ?_⟩
  intro R hR k z hcore
  let Good := fun q : SupportCellDescendant μ R hR k z =>
    bilateralBeta n μ q.center (1024 * q.radius) < ε
  obtain ⟨S, hS, hfit, f, hmodel, harea⟩ := hmodels R hR k z hcore
  exact ⟨S, hS, hfit, f, hmodel,
    active_region_limit_isClosedEmbedding μ R hR k z Good S hS ε hε
      (by linarith) hsmall hfit f hmodel, harea⟩

end

end RieszRectifiability

end OAI
