import OAI.NumberTheory.Jacobsthal.Paths.FlaggedSourceStart

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualCoupledHistories

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant PersistentFailureFlag
open FlaggedSourceStart ContinuousKilledBins FiniteHistoryTransport

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

noncomputable def sourceTransition (mesh : ℝ) :
    Kernel (FlagState (JointState w ell S start)) (FlagState (JointState w ell S start)) :=
  marked (jointKernel hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh)
    (mismatch_measurable mesh)

instance sourceTransition_markov (mesh : ℝ) :
    IsMarkovKernel (sourceTransition hw hell hS0 hS hr hs hsS mesh) := by
  unfold sourceTransition
  infer_instance

noncomputable def sourceHistoryLaw (mesh : ℝ) (n : ℕ) :
    Measure (Hist (FlagState (JointState w ell S start)) n) :=
  pathKernel (sourceTransition hw hell hS0 hS hr hs hsS mesh) n
    (fun _ => (sourceJoint w ell S start hs,false))

instance sourceHistoryLaw_probability (mesh : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n) := by
  unfold sourceHistoryLaw
  infer_instance

theorem sourceHistoryLaw_endpoint (mesh : ℝ) (n : ℕ) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n).map (last n) =
      sourceLaw hw hell hS0 hS hr hs hsS mesh n :=
  pathMeasure_endpoint _ n _

theorem sourceHistoryLaw_coordinate (mesh : ℝ) (n k : ℕ) (hk : k ≤ n) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n).map
      (fun h => h ⟨k, by simpa using hk⟩) = sourceLaw hw hell hS0 hS hr hs hsS mesh k :=
  pathMeasure_coordinate _ n k hk _

theorem sourceHistoryLaw_prime (mesh : ℝ) (n : ℕ) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n).map
      (mapHist (fun q => q.1.1) n) =
      pathKernel (chain w ell S start) n (fun _ => some History.empty) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  apply pathMeasure_mapHist _ _ (measurable_fst.comp measurable_fst)
  intro q
  calc
    _ = ((sourceTransition hw hell hS0 hS hr hs hsS mesh q).map Prod.fst).map Prod.fst :=
      (Measure.map_map measurable_fst measurable_fst).symm
    _ = _ := by
      rw [sourceTransition, marked_map]
      exact jointKernel_left hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh q.1.1 q.1.2

theorem sourceHistoryLaw_continuous (mesh : ℝ) (n : ℕ) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n).map
      (mapHist (fun q => q.1.2) n) =
      pathKernel (continuousChain (Real.log start.gap) ell S) n
        (fun _ => Sum.inl (sourceCostState hs)) := by
  apply pathMeasure_mapHist _ _ (measurable_snd.comp measurable_fst)
  intro q
  calc
    _ = ((sourceTransition hw hell hS0 hS hr hs hsS mesh q).map Prod.fst).map Prod.snd :=
      (Measure.map_map measurable_snd measurable_fst).symm
    _ = _ := by
      rw [sourceTransition, marked_map]
      exact jointKernel_right hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh q.1.1 q.1.2

end NumberTheoryLean.ActualCoupledHistories



namespace NumberTheoryLean.ActualSuccessfulHistories

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories FullHistoryFailureFlag
open ActualFlagInvariant FlaggedSourceStart FailureFlagBounds

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistory_no_reset (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N, noResetPath N h :=
  marked_history_no_reset _ (mismatch_measurable mesh) _ N

theorem sourceHistory_success_good {mesh : ℝ} (hm : 0 < mesh) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      (last N h).2 = false → ∀ j : Finset.Iic N,
        GoodAt (Real.log start.gap) mesh j.1 (h j).1 := by
  have hcoords : ∀ j : Finset.Iic N,
      ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
        surviving (GoodAt (Real.log start.gap) mesh j.1) (h j) := by
    intro j
    have hP := surviving_measurable (GoodAt_measurable (w:=w) (ell:=ell) (S:=S) (start:=start)
      (Real.log start.gap) mesh j.1)
    apply (ae_map_iff (measurable_pi_apply j).aemeasurable hP).mp
    have hcoord := sourceHistoryLaw_coordinate hw hell hS0 hS hr hs hsS mesh N j.1 (Finset.mem_Iic.mp j.2)
    rw [hcoord]
    exact sourceLaw_good hw hell hS0 hS hr hs hsS hm j.1
  have hAll := ae_all_iff.mpr hcoords
  filter_upwards [hAll,sourceHistory_no_reset hw hell hS0 hS hr hs hsS mesh N] with h hh hp
  intro hf j
  exact hh j (hp j hf)

theorem sourceHistory_failure_probability (mesh : ℝ) (N : ℕ) :
    sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N {h | (last N h).2 = true} =
      sourceLaw hw hell hS0 hS hr hs hsS mesh N failed := by
  rw [← sourceHistoryLaw_endpoint hw hell hS0 hS hr hs hsS mesh N,
    Measure.map_apply (last_measurable N) failed_measurable]
  rfl

end NumberTheoryLean.ActualSuccessfulHistories



namespace NumberTheoryLean.CanonicalCoupledHistories

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport CemeteryHistoryMap
open CemeteryKernel ContinuousKilledBins LowStateHorizon ActualCoupledHistories
open FlaggedSourceStart PrimeHistories ActualProcessCoupling

theorem canonical_killing_image (s : State) (n : ℕ) (v ell S : ℝ) :
    (finitePathMeasure s n).map (killHist (lowDomain v ell S) n) =
      pathKernel (continuousChain v ell S) n (fun _ => Sum.inl (s,0)) := by
  exact pathMeasure_killHist costKernel (lowDomain_measurable v ell S) n (fun _ => (s,0))

variable {w ell S : ℝ} {start : Node}
variable (hw : PrimeKilledChain.normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistoryLaw_canonical (mesh : ℝ) (n : ℕ) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n).map
      (mapHist (fun q => q.1.2) n) =
      (finitePathMeasure (typedState start.side start.ratio hs) n).map
        (killHist (lowDomain (Real.log start.gap) ell S) n) := by
  rw [sourceHistoryLaw_continuous,canonical_killing_image]
  rfl

theorem sourceHistoryLaw_canonical_event (mesh : ℝ) (n : ℕ)
    {A : Set (Hist (Space CostState) n)} (hA : MeasurableSet A) :
    sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n
        ((mapHist (fun q => q.1.2) n) ⁻¹' A) =
      finitePathMeasure (typedState start.side start.ratio hs) n
        ((killHist (lowDomain (Real.log start.gap) ell S) n) ⁻¹' A) := by
  have h := congrArg (fun μ : Measure (Hist (Space CostState) n) => μ A)
    (sourceHistoryLaw_canonical hw hell hS0 hS hr hs hsS mesh n)
  rwa [Measure.map_apply (by exact mapHist_measurable (by exact measurable_snd.comp measurable_fst) n) hA,
    Measure.map_apply (killHist_measurable (lowDomain_measurable _ _ _) n) hA] at h

end NumberTheoryLean.CanonicalCoupledHistories


end Erdos970

end OAI
