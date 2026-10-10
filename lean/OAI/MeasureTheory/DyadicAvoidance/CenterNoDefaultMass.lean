import OAI.MeasureTheory.DyadicAvoidance.CenterFailureBound
import OAI.MeasureTheory.DyadicAvoidance.RoutedExposure
import OAI.MeasureTheory.DyadicAvoidance.RoutedFirstDefault

namespace OAI

noncomputable section

namespace Problem310.CenterFailureBound

open Set MeasureTheory FiniteTableModel CenterRouteExposure RoutedSetDensity

/-- The atom-averaging bad event and the spatial router's no-default event
are identical, including their terminal-table coordinate. -/
theorem noDefaultEvent_eq_spatial {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ) (x : ℝ) :
    noDefaultEvent bS bT x =
      {ω : SelectorTable bS × TerminalTable bT | ∀ k < d,
        selectorChoice bS ω.1
          (RoutingPath.routeFrom (selectorChoice bS ω.1) k [] x) x ≠ Fin.last M} := by
  ext ω
  simp only [noDefaultEvent, Set.mem_ofPred_eq,
    RoutedExposure.routedPath_eq_centerRoute,
    RoutedExposure.selectorChoice_eq_centerChoice]

/-- Exact mass of the bad event in the concrete center-atom averaging theorem.
No probability or independence premises remain. -/
theorem outcomeLaw_noDefaultEvent {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1
      (noDefaultEvent bS bT x) = (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  rw [noDefaultEvent_eq_spatial]
  exact outcomeLaw_no_default_steps bS bT p hp0 hp1 x

/-- Concrete raw-failure assembly: only the numeric depth budget and the
per-good-atom local-trial estimate are required. -/
theorem raw_failure_le_of_outcome_center_atoms {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (B : SelectorTable bS × TerminalTable bT → Set ℝ) (N : Set ℕ) (x : ℝ)
    (htail : (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d ≤ ENNReal.ofReal p)
    (hatom : ∀ ξ : Node M d × Fin M → Bool, GoodExposure bS x ξ →
      ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1
        ({ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ∩
          centerAtom bS bT x ξ) ≤
        ENNReal.ofReal p *
          ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1
            (centerAtom bS bT x ξ)) :
    ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1
      {ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ≤
      ENNReal.ofReal (2 * p) := by
  apply raw_failure_le_of_center_atoms bS bT
    (ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1)
    p hp0 B N x _ hatom
  rw [outcomeLaw_noDefaultEvent]
  exact htail

end Problem310.CenterFailureBound

end

end OAI
