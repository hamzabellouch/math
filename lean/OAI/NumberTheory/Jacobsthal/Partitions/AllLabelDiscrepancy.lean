import OAI.NumberTheory.Jacobsthal.Estimates.CoupledBoundaryBounds

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.AllLabelDiscrepancy

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open MeshRatioLabels MeshBoundaryGeometry ActualSupportIntervals ActualProcessCoupling
open ContinuousKilledBins PrimeBinMembership RegeneratingInverseBands KernelBinConditioning
open CommonCellSum CouplingLabelEvents CoupledBoundaryEvents CoupledBoundaryBounds

theorem all_label_discrepancy : ∃ c₁ c₂ C₁ C₂ C₃ D w₀ : ℝ,
    0 < c₁ ∧ 0 < c₂ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ h : History w ell S start,
    ∀ v : ℝ, ∀ z : CostState, ∀ mesh : ℝ,
      normalizationThreshold ≤ w → 1 ≤ ell → 3 ≤ S → S ≤ (Real.log w)^3 →
      0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S → Consistent start →
      stateRatio z.1 ≤ S → h.node.side = stateSide z.1 → 0 < mesh →
      let Ld := minRatio h.node.side h.node.ratio
      let Lc := minRatio (stateSide z.1) (stateRatio z.1)
      let Ud := upperSupport S ell h.node.gap
      let Uc := upperSupport S ell (gapValue v z)
      |Ld-Lc|+mesh ≤ 1 → |Ud-Uc|+mesh ≤ 1 →
      (∑ j : Label S mesh, |labelMass (chain w ell S start) (primeLabel w ell S mesh start) (some h) j-
        labelMass (continuousChain v ell S) (continuousLabel S mesh) (.inl z) j|) ≤
      2*((S/mesh+2)*(C₁*(1+S)^5*(mesh^2+Real.exp (-c₁*Real.sqrt ((1/2:ℝ)*Real.log w))))+
        epsilon w+(Real.exp (D*(1+S)^3*|h.node.ratio-stateRatio z.1|)-1)+
        C₂*(1+S)^2*(|Ld-Lc|+|Ud-Uc|+2*mesh+2*Real.exp (-c₂*Real.sqrt ((1/2:ℝ)*Real.log w)))+
        C₃*(1+S)^2*(|Ld-Lc|+|Ud-Uc|+2*mesh)) := by
  classical
  obtain ⟨c₁,C₁,D,w₁,hc₁,hC₁,hD,hw₁,hcommon⟩ := common_cell_sum_error
  obtain ⟨c₂,C₂,w₂,hc₂,hC₂,hw₂,hprime⟩ := prime_bad_cells_upper
  obtain ⟨C₃,hC₃,hcontinuous⟩ := continuous_bad_cells_upper
  refine ⟨c₁,c₂,C₁,C₂,C₃,D,max w₁ w₂,hc₁,hc₂,hC₁,hC₂,hC₃,hD,
    hw₁.trans_le (le_max_left _ _),?_⟩
  intro w hw ell S start h v z mesh hnorm hell hS3 hS hr hs hsS hcons hzS hside hm
  dsimp only
  intro hL hU
  let Ld := minRatio h.node.side h.node.ratio
  let Lc := minRatio (stateSide z.1) (stateRatio z.1)
  let Ud := upperSupport S ell h.node.gap
  let Uc := upperSupport S ell (gapValue v z)
  let I := interiorLabels S mesh Ld Lc Ud Uc
  let δ := |Ld-Lc|+|Ud-Uc|+2*mesh
  let Bp := C₂*(1+S)^2*(δ+2*Real.exp (-c₂*Real.sqrt ((1/2:ℝ)*Real.log w)))
  let Bc := C₃*(1+S)^2*δ
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hBp : 0 ≤ Bp := by dsimp [Bp]; positivity
  have hBc : 0 ≤ Bc := by dsimp [Bc]; positivity
  have hi := hcommon w ((le_max_left _ _).trans hw) ell S start h v z mesh I
    hell hS3 hr hs hsS hcons hzS hside hm (fun j hj => (Finset.mem_filter.mp hj).2)
  have hp := hprime w ((le_max_right _ _).trans hw) ell S start hell hr hs hsS h mesh Lc Uc hm hL hU
  have hc := hcontinuous v ell S z (by linarith) hzS mesh Ld Ud hm
  have hpR : (chain w ell S start (some h) (primeBadCells mesh Ld Lc Ud Uc)).toReal ≤ Bp := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
    rwa [ENNReal.toReal_ofReal hBp] at h
  have hcR : (continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc)).toReal ≤ Bc := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
    rwa [ENNReal.toReal_ofReal hBc] at h
  have hb := actual_label_budget hnorm hell (by linarith) hS hr hs hsS h v z hm Ld Lc Ud Uc
  change (∑ j,_) ≤ _ at hb
  dsimp only [I,Bp,Bc,δ,Ld,Lc,Ud,Uc] at hi hpR hcR hb
  linarith

end NumberTheoryLean.AllLabelDiscrepancy


end Erdos970

end OAI
