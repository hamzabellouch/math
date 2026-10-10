import OAI.MeasureTheory.DyadicAvoidance.PeriodicBasic
import OAI.MeasureTheory.DyadicAvoidance.AdaptiveLabels
import OAI.MeasureTheory.DyadicAvoidance.AddressInjectivity
import OAI.MeasureTheory.DyadicAvoidance.CenterExposure
import OAI.MeasureTheory.DyadicAvoidance.CenterFailureBound
import OAI.MeasureTheory.DyadicAvoidance.CenterFirstDefault
import OAI.MeasureTheory.DyadicAvoidance.CenterNoDefaultMass
import OAI.MeasureTheory.DyadicAvoidance.CenterRouteExposure
import OAI.MeasureTheory.DyadicAvoidance.ChildDistribution
import OAI.MeasureTheory.DyadicAvoidance.ConcreteLabelMeasures
import OAI.MeasureTheory.DyadicAvoidance.ConcreteWindowAtom
import OAI.MeasureTheory.DyadicAvoidance.Construction
import OAI.MeasureTheory.DyadicAvoidance.DyadicRoutedAddresses
import OAI.MeasureTheory.DyadicAvoidance.ExceptionalCenters
import OAI.MeasureTheory.DyadicAvoidance.ExceptionalExpectation
import OAI.MeasureTheory.DyadicAvoidance.ExpectedRepair
import OAI.MeasureTheory.DyadicAvoidance.ExposureMoments
import OAI.MeasureTheory.DyadicAvoidance.ExposureUnionBound
import OAI.MeasureTheory.DyadicAvoidance.FiniteLocalHit
import OAI.MeasureTheory.DyadicAvoidance.FiniteLocalPredicate
import OAI.MeasureTheory.DyadicAvoidance.FiniteTableFirstDefault
import OAI.MeasureTheory.DyadicAvoidance.FiniteTableModel
import OAI.MeasureTheory.DyadicAvoidance.FirstDefault
import OAI.MeasureTheory.DyadicAvoidance.FirstDefaultSelection
import OAI.MeasureTheory.DyadicAvoidance.FixedScaleProbability
import OAI.MeasureTheory.DyadicAvoidance.GlobalFromPeriodic
import OAI.MeasureTheory.DyadicAvoidance.GridGeometry
import OAI.MeasureTheory.DyadicAvoidance.GridMeasure
import OAI.MeasureTheory.DyadicAvoidance.GridModelStability
import OAI.MeasureTheory.DyadicAvoidance.GridSeparation
import OAI.MeasureTheory.DyadicAvoidance.GridStability
import OAI.MeasureTheory.DyadicAvoidance.GridStabilityFin
import OAI.MeasureTheory.DyadicAvoidance.GridWindowStability
import OAI.MeasureTheory.DyadicAvoidance.LocalPredicateFactor
import OAI.MeasureTheory.DyadicAvoidance.MonotoneRepresentatives
import OAI.MeasureTheory.DyadicAvoidance.OrderedRoutePreservation
import OAI.MeasureTheory.DyadicAvoidance.OrderedRouting
import OAI.MeasureTheory.DyadicAvoidance.PackedWindowSpan
import OAI.MeasureTheory.DyadicAvoidance.PeriodicEnlargement
import OAI.MeasureTheory.DyadicAvoidance.PeriodicEnvelope
import OAI.MeasureTheory.DyadicAvoidance.PeriodicMeasure
import OAI.MeasureTheory.DyadicAvoidance.PreorderIndex
import OAI.MeasureTheory.DyadicAvoidance.RandomSetDensity
import OAI.MeasureTheory.DyadicAvoidance.RawRepair
import OAI.MeasureTheory.DyadicAvoidance.RepresentativeFailure
import OAI.MeasureTheory.DyadicAvoidance.RoutedAddressInjectivity
import OAI.MeasureTheory.DyadicAvoidance.RoutedExposure
import OAI.MeasureTheory.DyadicAvoidance.RoutedFirstDefault
import OAI.MeasureTheory.DyadicAvoidance.RoutedSetDensity
import OAI.MeasureTheory.DyadicAvoidance.RoutingBudget
import OAI.MeasureTheory.DyadicAvoidance.RoutingPath
import OAI.MeasureTheory.DyadicAvoidance.SelectedCoordinateLaw
import OAI.MeasureTheory.DyadicAvoidance.SelectorMoment
import OAI.MeasureTheory.DyadicAvoidance.StableKeyRouting
import OAI.MeasureTheory.DyadicAvoidance.StableRoutingBridge
import OAI.MeasureTheory.DyadicAvoidance.TreePreorder
import OAI.MeasureTheory.DyadicAvoidance.TreePreorderRank
import OAI.MeasureTheory.DyadicAvoidance.TreeSpanBridge
import OAI.MeasureTheory.DyadicAvoidance.TrialAddresses
import OAI.MeasureTheory.DyadicAvoidance.WindowBudgets
import OAI.MeasureTheory.DyadicAvoidance.WindowData
import OAI.MeasureTheory.DyadicAvoidance.WindowDataExistence
import OAI.MeasureTheory.DyadicAvoidance.WindowDataStability
import OAI.MeasureTheory.DyadicAvoidance.WindowExceptionalTransfer
import OAI.MeasureTheory.DyadicAvoidance.WindowFixedScale
import OAI.MeasureTheory.DyadicAvoidance.WindowLocalFactor
import OAI.MeasureTheory.DyadicAvoidance.WindowLocalHit
import OAI.MeasureTheory.DyadicAvoidance.WindowMetadata
import OAI.MeasureTheory.DyadicAvoidance.WindowPlacement
import OAI.MeasureTheory.DyadicAvoidance.WindowRecursion
import OAI.MeasureTheory.DyadicAvoidance.WindowSpanSum
import OAI.MeasureTheory.DyadicAvoidance.WindowTableModel
import OAI.MeasureTheory.DyadicAvoidance.WindowTrialAddresses

namespace OAI

noncomputable section

namespace Problem310

theorem periodic_hitting_set :
    ∀ p : ℝ, 0 < p → p < 1 → ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧ periodDensity H ≤ ENNReal.ofReal (6 * p) ∧ ∀ x t : ℝ, t ∈ Set.Icc (1 : ℝ) 2 → ∃ n : ℕ, 1 ≤ n ∧ x + t * dyadicPoint n ∈ H := by
  intro p hp hp1
  obtain ⟨M, d, R, hM, hd, hR, _, hsurvival, hbudget⟩ :=
    RoutingBudget.exists_nondefault_parameters p hp hp1
  obtain ⟨g, hg, hgeo⟩ := exists_windowData_selector_stability M d p hp
  let W := WindowConstruction.windowData (M + 1) d g R (by omega) hR
  obtain ⟨G, hG, hGp, hbad, hstable⟩ := hgeo R W
  apply Construction.periodic_hitting_of_window_failure W p hp hp1 G hG hbad
  intro x hx
  apply CenterFailureBound.raw_failure_le_of_outcome_center_atoms
    (FiniteTableModel.selectorEndpoints W) (FiniteTableModel.terminalEndpoints W)
    p hp.le hp1.le
    (RoutedSetDensity.routedSet (FiniteTableModel.selectorEndpoints W)
      (FiniteTableModel.terminalEndpoints W)) (Set.Ici 1) x
    (RoutingBudget.ennreal_survival_lt hp M d hsurvival).le
  intro ξ hξ
  apply ConcreteWindowAtom.raw_failure_on_good_atom W hM p hp.le hp1.le
    (fun r hr N hN => (hbudget r hr N hN).le) x ?_ ξ hξ
  intro P i n hn t ht ω
  exact (hstable x hx P i n hn t ht ω).symm

theorem dyadic_affine_avoidance :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasureTheory.volume E > ENNReal.ofReal (1 - η) ∧ ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x + s * dyadicPoint n ∉ E := by
  exact Problem310Support.avoidance_of_periodic_hitting periodic_hitting_set

end Problem310

end

end OAI
