import OAI.MeasureTheory.DyadicAvoidance.CenterFirstDefault
import OAI.MeasureTheory.DyadicAvoidance.FirstDefaultSelection

namespace OAI

noncomputable section

namespace Problem310.FiniteTableModel

/-- Exact no-default probability for the actual depth-`d` spatial router
under the finite selector/terminal outcome law. All randomness is instantiated. -/
theorem outcomeLaw_routed_no_default {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    (ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1)
      {ω : SelectorTable bS × TerminalTable bT |
        Fin.last M ∉ RoutingPath.routeFrom
          (fun P y => OrderedRouting.chooseChild (fun i => selectorValue bS ω.1 P i y))
          d [] x} = (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  have heq : {ω : SelectorTable bS × TerminalTable bT |
        Fin.last M ∉ RoutingPath.routeFrom
          (fun P y => OrderedRouting.chooseChild (fun i => selectorValue bS ω.1 P i y))
          d [] x} =
      ⋃ f : FirstDefault.Path M d, {ω : SelectorTable bS × TerminalTable bT |
        ∀ i : FirstDefault.Tests f,
          selectorValue bS ω.1 (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
            FirstDefault.requiredBit f i} := by
    ext ω
    exact FirstDefault.spatial_default_not_mem_iff
      (fun ω P i y => selectorValue bS ω.1 P i y) ω x
  rw [heq]
  exact outcomeLaw_center_no_default bS bT p hp0 hp1 x

/-- The same exact law stated with the step-by-step absence of a default.
This form pairs directly with first-default decomposition of the exposure atoms. -/
theorem outcomeLaw_no_default_steps {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    (ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1)
      {ω : SelectorTable bS × TerminalTable bT |
        ∀ k < d,
          OrderedRouting.chooseChild (fun i => selectorValue bS ω.1
            (RoutingPath.routeFrom
              (fun P y => OrderedRouting.chooseChild (fun i => selectorValue bS ω.1 P i y))
              k [] x) i x) ≠ Fin.last M} =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  convert outcomeLaw_routed_no_default bS bT p hp0 hp1 x using 1
  congr 1
  ext ω
  exact RoutingPath.noDefault_iff_not_mem
    (fun P y => OrderedRouting.chooseChild (fun i => selectorValue bS ω.1 P i y)) (Fin.last M) d x

end Problem310.FiniteTableModel

end

end OAI
