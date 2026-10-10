import OAI.NumberTheory.Jacobsthal.Primes.PrimeHistoryCompactCount
import OAI.NumberTheory.Jacobsthal.Renewal.NonnegativeOriginalOccupation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FullPathCompactSelection

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories PrimeHistoryCompactCount
open PrimeCompactVisits PrimeCompactWeights SourceCompactOccupation

variable {w ell S B : ℝ} {start : Node}

noncomputable def fullCompactReward (R w B : ℝ) {ell S : ℝ} (start : Node) (N : ℕ)
    (h : Hist (FlagState (JointState w ell S start)) N) : ℝ≥0∞ :=
  ∑ j : Fin N, compactReward R w B start (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1

theorem fullCompactReward_measurable (R w B : ℝ) {ell S : ℝ} (start : Node) (N : ℕ) :
    Measurable (fullCompactReward R w B (ell:=ell) (S:=S) start N) := by
  unfold fullCompactReward
  apply Finset.measurable_sum
  intro j _
  exact (measurable_of_countable (compactReward R w B start)).comp
    ((measurable_fst.comp measurable_fst).comp (measurable_pi_apply _))

theorem fullCompactReward_envelope {R D : ℝ}
    (hbound : ∀ h : History w ell S start, h.node.gap ≤ R → scaledWeight w B start (some h) ≤ D)
    (N : ℕ) (h : Hist (FlagState (JointState w ell S start)) N) :
    fullCompactReward R w B start N h ≤
      ENNReal.ofReal D * ENNReal.ofReal (pathSum (visit R) N (mapHist (fun q => q.1.1) N h)) := by
  unfold fullCompactReward pathSum mapHist
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => visit_nonneg _ _),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  exact compact_reward_envelope hbound _

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem selected_compact_history_bound {R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hbound : ∀ h : History w ell S start, h.node.gap ≤ R → scaledWeight w B start (some h) ≤ D)
    (mesh : ℝ) (N : ℕ) {A : Set (Hist (FlagState (JointState w ell S start)) N)}
    (hA : MeasurableSet A) :
    (∫⁻ h, A.indicator (fullCompactReward R w B start N) h
      ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N) ≤
      ENNReal.ofReal (D*(R+1)) * sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N A := by
  calc
    _ ≤ ∫⁻ h, A.indicator (fun _ => ENNReal.ofReal (D*(R+1))) h
        ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N := by
      apply lintegral_mono_ae
      filter_upwards [sourceHistory_compact_count hw hell hS0 hS hr hs hsS hR mesh N] with h hh
      apply Set.indicator_le_indicator
      refine (fullCompactReward_envelope hbound N h).trans ?_
      rw [ENNReal.ofReal_mul hD]
      exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hh) zero_le
    _ = _ := lintegral_indicator_const hA _

end NumberTheoryLean.FullPathCompactSelection

end

end Erdos970

end OAI
