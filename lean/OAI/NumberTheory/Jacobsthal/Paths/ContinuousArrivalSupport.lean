import OAI.NumberTheory.Jacobsthal.Probability.SourceCompactCoupling
import OAI.NumberTheory.Jacobsthal.Renewal.ContinuousCompletedOccupation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousArrivalSupport

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins CemeteryKernel LowStateHorizon ArrivalKernelGeometry

def arrivalSupported (v ell : ℝ) : Space CostState → Prop
  | .inl z => z ∈ arrivalSet v ell
  | .inr _ => True

theorem arrivalSupported_measurable (v ell : ℝ) : MeasurableSet {z | arrivalSupported v ell z} := by
  apply measurableSet_sum_iff.mpr
  exact ⟨arrivalSet_measurable v ell,MeasurableSet.univ⟩

theorem unsupported_eq (v ell : ℝ) :
    {z : Space CostState | ¬arrivalSupported v ell z} = Sum.inl '' (arrivalSet v ell)ᶜ := by
  ext z
  cases z <;> simp [arrivalSupported]

theorem continuous_row_arrival (v ell S : ℝ) (q : Space CostState) :
    ∀ᵐ y ∂continuousChain v ell S q,arrivalSupported v ell y := by
  apply ae_iff.mpr
  rw [unsupported_eq]
  cases q with
  | inl z =>
    rw [continuousChain,complete_live_mass _ _ (arrivalSet_measurable v ell).compl,
      lowKernel,Kernel.restrict_apply,Measure.restrict_apply (arrivalSet_measurable v ell).compl]
    have he : (arrivalSet v ell)ᶜ ∩ lowDomain v ell S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hy.1 hy.2.1
    rw [he,measure_empty]
  | inr u =>
    cases u
    change Measure.dirac (dead : Space CostState) (Sum.inl '' (arrivalSet v ell)ᶜ) = 0
    rw [Measure.dirac_apply' _ (arrivalSet_measurable v ell).compl.inl_image,
      indicator_of_notMem (by simp [dead])]

theorem continuous_power_arrival (v ell S : ℝ) (q : Space CostState) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ y ∂((continuousChain v ell S)^n) q,arrivalSupported v ell y := by
  cases n with
  | zero => omega
  | succ n =>
    have hp : (continuousChain v ell S)^(n+1) = continuousChain v ell S ∘ₖ ((continuousChain v ell S)^n) := pow_succ' _ _
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (arrivalSupported_measurable v ell)
    exact Filter.Eventually.of_forall (continuous_row_arrival v ell S)

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hw hell hS0 hS hr hsS in

theorem source_arrival (mesh : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ q ∂CouplingData.sourceLaw w ell S start hs mesh n,
      arrivalSupported (Real.log start.gap) ell q.1.2 := by
  have he := FlaggedSourceStart.sourceLaw_continuous hw hell hS0 hS hr hs hsS mesh n
  rw [CouplingData.sourceLaw_eq hw hell hS0 hS hr hs hsS] at he
  have h : ∀ᵐ y ∂(CouplingData.sourceLaw w ell S start hs mesh n).map (fun q => q.1.2),
      arrivalSupported (Real.log start.gap) ell y := by
    rw [he]
    exact continuous_power_arrival _ _ _ _ n hn
  exact (ae_map_iff (measurable_snd.comp measurable_fst).aemeasurable
    (arrivalSupported_measurable _ _)).mp h

end NumberTheoryLean.ContinuousArrivalSupport

end

end Erdos970

end OAI
