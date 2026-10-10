import OAI.NumberTheory.Jacobsthal.Partitions.AllLabelDiscrepancy

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualCouplingError

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open MeshRatioLabels ActualSupportIntervals ActualProcessCoupling
open PrimeBinMembership RegeneratingInverseBands AllLabelDiscrepancy

theorem actual_one_step_failure : ∃ c₁ c₂ C₁ C₂ C₃ D w₀ : ℝ,
    0 < c₁ ∧ 0 < c₂ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ h : History w ell S start,
    ∀ v : ℝ, ∀ z : CostState, ∀ mesh : ℝ,
      ∀ (hnorm : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS3 : 3 ≤ S) (hS : S ≤ (Real.log w)^3)
        (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S), Consistent start →
      stateRatio z.1 ≤ S → h.node.side = stateSide z.1 → 0 < mesh →
      let Ld := minRatio h.node.side h.node.ratio
      let Lc := minRatio (stateSide z.1) (stateRatio z.1)
      let Ud := upperSupport S ell h.node.gap
      let Uc := upperSupport S ell (gapValue v z)
      |Ld-Lc|+mesh ≤ 1 → |Ud-Uc|+mesh ≤ 1 →
      jointKernel hnorm hell (show 0 ≤ S from (by linarith)) hS hr hs hsS v mesh (some h,.inl z)
        {q | primeLabel w ell S mesh start q.1 ≠ continuousLabel S mesh q.2} ≤
      ENNReal.ofReal (2*((S/mesh+2)*(C₁*(1+S)^5*(mesh^2+Real.exp (-c₁*Real.sqrt ((1/2:ℝ)*Real.log w))))+
        epsilon w+(Real.exp (D*(1+S)^3*|h.node.ratio-stateRatio z.1|)-1)+
        C₂*(1+S)^2*(|Ld-Lc|+|Ud-Uc|+2*mesh+2*Real.exp (-c₂*Real.sqrt ((1/2:ℝ)*Real.log w)))+
        C₃*(1+S)^2*(|Ld-Lc|+|Ud-Uc|+2*mesh))) := by
  obtain ⟨c₁,c₂,C₁,C₂,C₃,D,w₀,hc₁,hc₂,hC₁,hC₂,hC₃,hD,hw₀,hbound⟩ := all_label_discrepancy
  refine ⟨c₁,c₂,C₁,C₂,C₃,D,w₀,hc₁,hc₂,hC₁,hC₂,hC₃,hD,hw₀,?_⟩
  intro w hw ell S start h v z mesh hnorm hell hS3 hS hr hs hsS hcons hzS hside hm
  dsimp only
  intro hL hU
  exact (jointKernel_mismatch_bound hnorm hell (by linarith) hS hr hs hsS v mesh (some h) (.inl z)).trans
    (ENNReal.ofReal_le_ofReal (hbound w hw ell S start h v z mesh hnorm hell hS3 hS hr hs hsS hcons hzS hside hm hL hU))

end NumberTheoryLean.ActualCouplingError


end Erdos970

end OAI
