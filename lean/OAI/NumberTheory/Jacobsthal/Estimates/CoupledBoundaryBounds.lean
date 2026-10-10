import OAI.NumberTheory.Jacobsthal.Probability.CouplingLabelEvents

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CoupledBoundaryBounds

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualSupportIntervals CoupledBoundaryEvents PrimeCompletedIntervalUpper
open ContinuousIntervalUpper RegeneratingInverseBands ContinuousKilledBins

theorem prime_bad_cells_upper : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S →
      ∀ h : History w ell S start, ∀ mesh Lc Uc : ℝ, 0 < mesh →
      let Ld := minRatio h.node.side h.node.ratio
      let Ud := upperSupport S ell h.node.gap
      |Ld-Lc|+mesh ≤ 1 → |Ud-Uc|+mesh ≤ 1 →
      chain w ell S start (some h) (primeBadCells mesh Ld Lc Ud Uc) ≤
        ENNReal.ofReal (C*(1+S)^2*(|Ld-Lc|+|Ud-Uc|+2*mesh+
          2*Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w)))) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := prime_completed_interval_upper
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw ell S start hell hr hs hsS h mesh Lc Uc hm
  dsimp only
  intro hL hU
  let Ld := minRatio h.node.side h.node.ratio
  let Ud := upperSupport S ell h.node.gap
  let e := Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))
  have hwid := packet_widths hm.le Ld Lc Ud Uc
  have hleft := hbound w hw ell S start hell hr hs hsS h (lowerA Ld Lc) (lowerB mesh Ld Lc)
    hwid.1.1 hwid.1.2.1 (hwid.1.2.2.trans hL)
  have hright := hbound w hw ell S start hell hr hs hsS h (upperA mesh Ud Uc) (upperB Ud Uc)
    hwid.2.1 hwid.2.2.1 (hwid.2.2.2.trans hU)
  have hM : 0 ≤ C*(1+S)^2 := by positivity
  have he : 0 ≤ e := (Real.exp_pos _).le
  calc
    _ ≤ chain w ell S start (some h) (closedLiveBin (lowerA Ld Lc) (lowerB mesh Ld Lc))+
        chain w ell S start (some h) (closedLiveBin (upperA mesh Ud Uc) (upperB Ud Uc)) :=
      prime_bad_cell_packets h (by linarith) hr hs hsS hm Lc Uc
    _ ≤ ENNReal.ofReal (C*(1+S)^2*(lowerB mesh Ld Lc-lowerA Ld Lc+e))+
        ENNReal.ofReal (C*(1+S)^2*(upperB Ud Uc-upperA mesh Ud Uc+e)) := add_le_add hleft hright
    _ = ENNReal.ofReal (C*(1+S)^2*((lowerB mesh Ld Lc-lowerA Ld Lc)+
        (upperB Ud Uc-upperA mesh Ud Uc)+2*e)) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hM (by linarith [hwid.1.2.1]))
        (mul_nonneg hM (by linarith [hwid.2.2.1]))]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (by linarith [hwid.1.2.2,hwid.2.2.2]) hM)

theorem continuous_bad_cells_upper : ∃ C : ℝ, 0 < C ∧ ∀ v ell S : ℝ, ∀ z : CostState,
    0 < ell → stateRatio z.1 ≤ S → ∀ mesh Ld Ud : ℝ, 0 < mesh →
      let Lc := minRatio (stateSide z.1) (stateRatio z.1)
      let Uc := upperSupport S ell (gapValue v z)
      continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc) ≤
        ENNReal.ofReal (C*(1+S)^2*(|Ld-Lc|+|Ud-Uc|+2*mesh)) := by
  obtain ⟨C,hC,hbound⟩ := completed_interval_upper
  refine ⟨C,hC,?_⟩
  intro v ell S z hell hsS mesh Ld Ud hm
  dsimp only
  let Lc := minRatio (stateSide z.1) (stateRatio z.1)
  let Uc := upperSupport S ell (gapValue v z)
  have hwid := packet_widths hm.le Ld Lc Ud Uc
  have hleft := hbound v ell S (lowerA Ld Lc) (lowerB mesh Ld Lc) z hsS
  have hright := hbound v ell S (upperA mesh Ud Uc) (upperB Ud Uc) z hsS
  have hM : 0 ≤ C*(1+S)^2 := by positivity
  rw [← ENNReal.ofReal_mul hM] at hleft hright
  calc
    _ ≤ continuousChain v ell S (.inl z) (Sum.inl '' closedCostBin (lowerA Ld Lc) (lowerB mesh Ld Lc))+
        continuousChain v ell S (.inl z) (Sum.inl '' closedCostBin (upperA mesh Ud Uc) (upperB Ud Uc)) :=
      continuous_bad_cell_packets v z hell hm Ld Ud
    _ ≤ ENNReal.ofReal (C*(1+S)^2*(lowerB mesh Ld Lc-lowerA Ld Lc))+
        ENNReal.ofReal (C*(1+S)^2*(upperB Ud Uc-upperA mesh Ud Uc)) := add_le_add hleft hright
    _ = ENNReal.ofReal (C*(1+S)^2*((lowerB mesh Ld Lc-lowerA Ld Lc)+
        (upperB Ud Uc-upperA mesh Ud Uc))) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hM (sub_nonneg.mpr hwid.1.2.1))
        (mul_nonneg hM (sub_nonneg.mpr hwid.2.2.1))]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (by linarith [hwid.1.2.2,hwid.2.2.2]) hM)

end NumberTheoryLean.CoupledBoundaryBounds


end Erdos970

end OAI
