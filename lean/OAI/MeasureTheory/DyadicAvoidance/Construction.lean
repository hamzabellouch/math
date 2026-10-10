import OAI.MeasureTheory.DyadicAvoidance.RawRepair
import OAI.MeasureTheory.DyadicAvoidance.WindowTableModel
import OAI.MeasureTheory.DyadicAvoidance.RoutedSetDensity
import OAI.MeasureTheory.DyadicAvoidance.ConcreteLabelMeasures
import OAI.MeasureTheory.DyadicAvoidance.RoutingBudget

namespace OAI

noncomputable section

namespace Problem310.Construction

open Set MeasureTheory FiniteTableModel

/-- The analytic conclusion for the actual finite window-table model. All
regularity and first-moment obligations are discharged here; only the geometric
good-center set and its raw failure estimate remain as inputs. -/
theorem periodic_hitting_of_window_failure
    {M d g r₀ : ℕ} (W : WindowData (M + 1) d g r₀)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (G : Set ℝ) (hG : MeasurableSet G)
    (hbad : volume (Gᶜ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p)
    (hgood : ∀ x ∈ G,
      ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
        (TerminalAddress (terminalEndpoints W)) p hp.le hp1.le
        {ω | x ∈ Auxiliary.exceptionalCenters
          (RoutedSetDensity.routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
          (Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n)} ≤ ENNReal.ofReal (2 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  classical
  apply Auxiliary.periodic_hitting_of_raw_construction
    (ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp.le hp1.le)
    p hp (RoutedSetDensity.routedSet (selectorEndpoints W) (terminalEndpoints W))
    (RoutedSetDensity.routedSet_periodic _ _) (Ici 1) (fun _ hn => hn)
    G hG hbad
  · have hmean := RoutedSetDensity.expected_routedSet_density
      (selectorEndpoints W) (terminalEndpoints W)
      (ConcreteLabels.selectorLaw (SelectorAddress (selectorEndpoints W)))
      (ConcreteLabels.bitLaw p hp.le hp1.le)
    simpa only [ConcreteLabels.outcomeLaw, ConcreteLabels.terminalLaw,
      ConcreteLabels.bitLaw_true] using hmean.le
  · exact hgood

end Problem310.Construction

end

end OAI
