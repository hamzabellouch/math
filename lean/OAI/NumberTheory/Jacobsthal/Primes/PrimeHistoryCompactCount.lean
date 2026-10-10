import OAI.NumberTheory.Jacobsthal.Estimates.CanonicalCoupledHistories

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeHistoryCompactCount

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactVisits
open FiniteHistoryTransport ActualCoupledHistories ActualProcessCoupling PersistentFailureFlag

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hw hell hS0 hS hr hs hsS

theorem pathwise_compact_potential {R : ℝ} (hR : 0 ≤ R) (N : ℕ) :
    ∀ᵐ h ∂pathKernel (chain w ell S start) N (fun _ => some History.empty),
      pathSum (visit R) N h + potential R (last N h) ≤
        potential R (some (History.empty : History w ell S start)) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  have hv : Measurable (visit (w:=w) (ell:=ell) (S:=S) (start:=start) R) := measurable_of_countable _
  have hp : Measurable (potential (w:=w) (ell:=ell) (S:=S) (start:=start) R) := measurable_of_countable _
  induction N with
  | zero =>
    change ∀ᵐ h ∂Measure.dirac (fun _ => some History.empty), _
    apply (ae_dirac_iff ((measurableSet_le
      ((pathSum_measurable hv 0).add (hp.comp (last_measurable 0))) measurable_const))).mpr
    simp [pathSum,last]
  | succ N ih =>
    apply ae_pathKernel_succ _ N _ (measurableSet_le
      ((pathSum_measurable hv (N+1)).add (hp.comp (last_measurable (N+1)))) measurable_const)
    filter_upwards [ih] with h hh
    filter_upwards [actual_row_drift_ae hell hr hs hR (last N h)] with y hy
    change pathSum (visit R) (N+1) (FiniteHistoryTransport.extend N h y) +
      potential R (last (N+1) (FiniteHistoryTransport.extend N h y)) ≤ _
    rw [pathSum_extend,extend_last]
    linarith

theorem pathwise_compact_count {R : ℝ} (hR : 0 ≤ R) (N : ℕ) :
    ∀ᵐ h ∂pathKernel (chain w ell S start) N (fun _ => some History.empty),
      pathSum (visit R) N h ≤ R+1 := by
  filter_upwards [pathwise_compact_potential hw hell hS0 hS hr hs hsS hR N] with h hh
  have hp := potential_nonneg hR (by linarith : 0 ≤ ell) hr hs (last N h)
  have hinit := potential_le (w:=w) (ell:=ell) (S:=S) (start:=start) hR (some History.empty)
  linarith

theorem sourceHistory_compact_count {R : ℝ} (hR : 0 ≤ R) (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      pathSum (visit R) N (mapHist (fun q => q.1.1) N h) ≤ R+1 := by
  have hP : MeasurableSet {h : Hist (ChainState w ell S start) N |
      pathSum (visit R) N h ≤ R+1} :=
    measurableSet_le (pathSum_measurable (measurable_of_countable _) N) measurable_const
  have hh : ∀ᵐ h ∂(sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N).map
      (mapHist (fun q => q.1.1) N), pathSum (visit R) N h ≤ R+1 := by
    rw [sourceHistoryLaw_prime]
    exact pathwise_compact_count hw hell hS0 hS hr hs hsS hR N
  exact (ae_map_iff (mapHist_measurable (by exact measurable_fst.comp measurable_fst) N).aemeasurable hP).mp hh

end NumberTheoryLean.PrimeHistoryCompactCount

end

end Erdos970

end OAI
