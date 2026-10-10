import OAI.MeasureTheory.DyadicAvoidance.WindowTrialAddresses
import OAI.MeasureTheory.DyadicAvoidance.FixedScaleProbability
import OAI.MeasureTheory.DyadicAvoidance.ConcreteLabelMeasures

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem310.WindowTrialAddresses

open FiniteTableModel ConcreteLabels

variable {M d g r₀ : ℕ}

/-- Exact fixed-scale failure mass for the actual W-indexed finite table
model. All fresh-selector and adaptive-terminal injectivity obligations are
discharged here; local leaves only have to stay in their selected child. -/
theorem window_fixed_scale_on_center_atom
    (W : WindowData (M + 1) d g r₀) (P : Node M d) (x t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (value : Node M d × Fin M → Bool)
    (leaf : SelectorTable (selectorEndpoints W) → LocalTrial W P → Leaf M d)
    (hprefix : ∀ a z, (selectorEdge P z.1).IsPrefix (leaf a z).val) :
    outcomeLaw (SelectorAddress (selectorEndpoints W)) (TerminalAddress (terminalEndpoints W))
      p hp0 hp1
      {z : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W) |
        (∀ c : Node M d × Fin M,
          z.1 (selectorAddress (selectorEndpoints W) c.1 c.2 x) = value c) ∧
        ∀ i : LocalTrial W P, z.1 (localSelectorAddress W P x t i) = true →
          z.2 (terminalAddress (terminalEndpoints W) (leaf z.1 i)
            (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P i))) = false} =
      selectorLaw (SelectorAddress (selectorEndpoints W))
        {a | ∀ c : Node M d × Fin M,
          a (selectorAddress (selectorEndpoints W) c.1 c.2 x) = value c} *
      (ENNReal.ofReal (1 - p / 2)) ^ (M * W.r (d - P.val.length)) := by
  classical
  have h := FixedScaleProbability.measure_fixed_scale_eq_atom_mass
    fairLaw (bitLaw p hp0 hp1)
    (by simpa only [one_div] using fairLaw_singleton false)
    (by simpa only [one_div] using fairLaw_singleton true)
    (fun c : Node M d × Fin M => selectorAddress (selectorEndpoints W) c.1 c.2 x)
    (localSelectorAddress W P x t) (center_local_sum_injective W P x t ht) value
    (fun a i => terminalAddress (terminalEndpoints W) (leaf a i)
      (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P i)))
    (fun a => localTerminalAddress_injective W P x t ht (leaf a) (hprefix a))
    p hp1 (bitLaw_false p hp0 hp1)
  simpa only [outcomeLaw, selectorLaw, terminalLaw, card_localTrial] using h

end Problem310.WindowTrialAddresses

end

end OAI
