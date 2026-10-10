import OAI.NumberTheory.Jacobsthal.Estimates.CanonicalCoupledHistories

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SourceTransitionSupport
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCoupledHistories ActualFlagInvariant PersistentFailureFlag
open ActualCouplingUpdates ActualSupportIntervals ContinuousKilledBins LowStateHorizon


variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceTransition_left (mesh : ℝ) (x : FlagState (JointState w ell S start)) :
    (sourceTransition hw hell hS0 hS hr hs hsS mesh x).map (fun y => y.1.1)=chain w ell S start x.1.1 := by
  calc
    _ = ((sourceTransition hw hell hS0 hS hr hs hsS mesh x).map Prod.fst).map Prod.fst :=
      (Measure.map_map measurable_fst measurable_fst).symm
    _ = _ := by
      rw [sourceTransition,marked_map]
      exact jointKernel_left hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh x.1.1 x.1.2

theorem sourceTransition_right (mesh : ℝ) (x : FlagState (JointState w ell S start)) :
    (sourceTransition hw hell hS0 hS hr hs hsS mesh x).map (fun y => y.1.2)=
      continuousChain (Real.log start.gap) ell S x.1.2 := by
  calc
    _ = ((sourceTransition hw hell hS0 hS hr hs hsS mesh x).map Prod.fst).map Prod.snd :=
      (Measure.map_map measurable_snd measurable_fst).symm
    _ = _ := by
      rw [sourceTransition,marked_map]
      exact jointKernel_right hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh x.1.1 x.1.2

theorem sourceTransition_live_support (mesh : ℝ) (h : History w ell S start) (z : CostState) (flag : Bool) :
    ∀ᵐ y ∂sourceTransition hw hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag),
      primeFollows h y.1.1 ∧ liftPredicate
        (fun q : CostState => minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio q.1) y.1.2 := by
  have hp : ∀ᵐ y ∂sourceTransition hw hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag),primeFollows h y.1.1 := by
    have hh : ∀ᵐ y ∂(sourceTransition hw hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag)).map
        (fun y => y.1.1),primeFollows h y := by
      rw [sourceTransition_left hw hell hS0 hS hr hs hsS]
      exact prime_follows h
    exact (ae_map_iff (measurable_fst.comp measurable_fst).aemeasurable (show MeasurableSet {y | primeFollows h y} from trivial)).mp hh
  have hP : MeasurableSet {q : CostState | minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio q.1} :=
    measurableSet_le measurable_const (stateRatio_measurable.comp measurable_fst)
  have hq : ∀ᵐ y ∂sourceTransition hw hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag),
      liftPredicate (fun q : CostState => minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio q.1) y.1.2 := by
    have hh : ∀ᵐ y ∂(sourceTransition hw hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag)).map
        (fun y => y.1.2),liftPredicate (fun q : CostState => minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio q.1) y := by
      rw [sourceTransition_right hw hell hS0 hS hr hs hsS]
      apply complete_ae _ z hP
      rw [lowKernel,Kernel.restrict_apply]
      exact ae_restrict_of_ae (costKernel_lower_support z)
    exact (ae_map_iff (measurable_snd.comp measurable_fst).aemeasurable (liftPredicate_measurable hP)).mp hh
  exact hp.and hq
end NumberTheoryLean.SourceTransitionSupport


end Erdos970

end OAI
