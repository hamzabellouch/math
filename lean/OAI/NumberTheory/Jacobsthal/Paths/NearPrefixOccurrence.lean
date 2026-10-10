import OAI.NumberTheory.Jacobsthal.Primes.AdjacentPrimeRecovery
import OAI.NumberTheory.Jacobsthal.Primes.FullHistoryPrimeOccupation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CompactPrefixOccurrence

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories SourceSelectedCompactOccupation
open FullHistoryPrimeOccupation FullPathCompactSelection SourceCompactOccupation
open PrimeCompactWeights PrimeCompactVisits PrimeFamilyOccupation

attribute [local instance] Classical.propDecidable

variable {w ell S B R : ℝ} {start : Node}

def selectedNode (E : Set (List ℕ)) : ChainState w ell S start → Prop
  | none => False
  | some h => h.primes ∈ E

def occurs (E : Set (List ℕ)) (N : ℕ)
    (h : Hist (FlagState (JointState w ell S start)) N) : Prop :=
  ∃ j : Fin N, selectedNode E (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1

theorem occurs_measurable (E : Set (List ℕ)) (N : ℕ) :
    MeasurableSet {h : Hist (FlagState (JointState w ell S start)) N | occurs E N h} := by
  simp only [occurs,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  have hm : Measurable (fun h : Hist (FlagState (JointState w ell S start)) N =>
      (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1) := by fun_prop
  exact hm (show MeasurableSet {z : ChainState w ell S start | selectedNode E z} from by trivial)

noncomputable def listSelection (E : Set (List ℕ)) (ps : List ℕ) : ℝ :=
  if ps ∈ E then 1 else 0

theorem listSelection_nonneg (E : Set (List ℕ)) (ps : List ℕ) : 0 ≤ listSelection E ps := by
  unfold listSelection
  split_ifs <;> norm_num

theorem selected_node_compact (E : Set (List ℕ))
    (hcompact : ∀ h : History w ell S start,h.primes ∈ E → h.node.gap ≤ R)
    (z : ChainState w ell S start) :
    ENNReal.ofReal (scaledWeight w B start z*listReward (listSelection E) z) ≤
      compactReward R w B start z := by
  cases z with
  | none => simp [scaledWeight,listReward,compactReward,visit]
  | some h =>
    by_cases he : h.primes ∈ E
    · simp [listReward,listSelection,he,compactReward,visit,hcompact h he]
    · simp [listReward,listSelection,he]

theorem full_selected_le_occurrence (E : Set (List ℕ))
    (hcompact : ∀ h : History w ell S start,h.primes ∈ E → h.node.gap ≤ R)
    (N : ℕ) (h : Hist (FlagState (JointState w ell S start)) N) :
    fullListReward w B start (listSelection E) N h ≤
      {h | occurs E N h}.indicator (fullCompactReward R w B start N) h := by
  by_cases ho : occurs E N h
  · rw [Set.indicator_of_mem (show h ∈ {h | occurs E N h} from ho)]
    exact Finset.sum_le_sum (fun j _ => selected_node_compact E hcompact _)
  · rw [Set.indicator_of_notMem (show h ∉ {h | occurs E N h} from ho)]
    apply le_of_eq
    unfold fullListReward
    apply Finset.sum_eq_zero
    intro j _
    have hj : ¬selectedNode E (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1 :=
      fun hj => ho ⟨j,hj⟩
    cases hz : (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1 with
    | none => simp [scaledWeight,listReward]
    | some p =>
      rw [hz] at hj
      change p.primes ∉ E at hj
      simp [listReward,listSelection,hj]

end NumberTheoryLean.CompactPrefixOccurrence

end

section

namespace NumberTheoryLean.NearPrefixOccurrence
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain FiniteHistoryTransport
open ActualCoupledHistories PrimePrefixRecovery SourceThresholdCoupling
open CompactPrefixOccurrence SourceSelectedCompactOccupation

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem selected_near_prefix_occurs (mesh delta : ℝ) (N : ℕ) (E : Set (List ℕ))
    (hE : ∀ p : History w ell S start,p.primes ∈ E → hasNearThresholdPrefix w delta start p.primes) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      occurs E N h → primeThresholdOccurs delta N h := by
  filter_upwards [recovered_near_prefix_occurs hw hell hS0 hS hr hs hsS mesh delta N] with h hh
  rintro ⟨j,hj⟩
  let k : Finset.Iic N := ⟨j.1,Finset.mem_Iic.mpr j.isLt.le⟩
  change selectedNode E ((h k).1.1) at hj
  cases hp : (h k).1.1 with
  | none => rw [hp] at hj; exact False.elim hj
  | some p =>
    rw [hp] at hj
    exact hh k p hp (hE p hj)

include hw hell hS0 hS hr hsS in
theorem near_prefix_occurrence_probability (mesh delta : ℝ) (N : ℕ) (E : Set (List ℕ))
    (hE : ∀ p : History w ell S start,p.primes ∈ E → hasNearThresholdPrefix w delta start p.primes) :
    fullSourceLaw w ell S start hs mesh N {h | occurs E N h} ≤
      fullSourceLaw w ell S start hs mesh N {h | primeThresholdOccurs delta N h} := by
  rw [fullSourceLaw_eq hw hell hS0 hS hr hs hsS]
  exact measure_mono_ae (selected_near_prefix_occurs hw hell hS0 hS hr hs hsS mesh delta N E hE)
end NumberTheoryLean.NearPrefixOccurrence

end

end Erdos970

end OAI
