import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.RecoveryCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.GroupAssignment

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupMasks

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryMasks AllFieldHistoryRawMasks AllFieldHistoryIncomingMasks
open JointPopulation JointCanonicalization JointCanonicalCW InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def groupCounts (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (h : ActiveOrder K tick sigma) : JointPopulation.Shape → ℕ :=
  activeCounts allocation m h.val

abbrev GroupRaw (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  RawPairs (groupCounts (K := K) (tick := tick) allocation m sigma)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)

def projectRaw (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    GroupRaw (K := K) (tick := tick) allocation m sigma := fun h j => w h.val j

def marginal (allocation : Allocation) (m : ℕ) (side : Fin 3) (sigma : Placement)
    (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∀ (h : ActiveOrder K tick sigma) a,
    wordPopulation (fun j => coarse activeHalfLength activeHalfLength
      AllFieldHistoryRecovery.halfLength_le_eight side h.val (w h j)) a =
    wordPopulation (sideWord (activeCounts allocation m) side
      (triple (activeCounts allocation m) (canonicalTarget (activeCounts allocation m))) h.val) a

def incoming (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (h : ActiveOrder K tick sigma) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) :
    HistoryWord allocation m (h.val.val.1.source, h.val.val.2) :=
  fun p => joinHalves h.val.val.1
    (w h ((sourcePositionsEquiv allocation m h.val).symm p))

def received (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (sigma : Placement) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∀ h : ActiveOrder K tick sigma,
    residentMask allocation m ε (h.val.val.1.source, h.val.val.2) side
      (incoming allocation m sigma h w)

def rawPass (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (sigma : Placement) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∀ (i : MaskIndex K tick) (hi : i.1.val.physicalOrder = sigma),
    |(∑ j : JointPopulation.Positions (activeCounts allocation m) i.1,
        if statistic i.1 (w ⟨i.1, hi⟩ j).1 = i.2.1 i.1 ∧
          statistic i.1 (w ⟨i.1, hi⟩ j).2 = i.2.2 i.1 then (1 : ℝ) else 0) /
        (population allocation m (i.1.val.1.source, i.1.val.2) : ℝ) -
      center allocation side i| ≤ pairWidth ε i.1

def completeKeep (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (sigma : Placement) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  marginal allocation m side sigma w ∧ received allocation m ε side sigma w ∧
    rawPass allocation m ε side sigma w

theorem marginal_project (allocation : Allocation) (m : ℕ) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : JointCanonicalMixed.sideMask (activeCounts allocation m)
      activeHalfLength activeHalfLength AllFieldHistoryRecovery.halfLength_le_eight side w)
    (sigma : Placement) : marginal allocation m side sigma (projectRaw allocation m sigma w) := by
  intro h a
  exact hw h.val a

theorem received_project (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryIncomingMasks.received allocation m ε side w)
    (sigma : Placement) : received allocation m ε side sigma (projectRaw allocation m sigma w) := by
  intro h
  exact hw h.val

theorem rawPass_project (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRawMasks.rawPass allocation m ε side w)
    (sigma : Placement) : rawPass allocation m ε side sigma (projectRaw allocation m sigma w) := by
  intro i hi
  exact hw i

theorem completeKeep_project (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRecovery.completeKeep allocation m ε side w)
    (sigma : Placement) : completeKeep allocation m ε side sigma
      (projectRaw allocation m sigma w) :=
  ⟨marginal_project allocation m side w hw.1 sigma,
    received_project allocation m ε side w hw.2.1 sigma,
    rawPass_project allocation m ε side w hw.2.2 sigma⟩

theorem completeKeep_iff_all_groups (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    AllFieldHistoryRecovery.completeKeep allocation m ε side w ↔
      ∀ sigma, completeKeep allocation m ε side sigma (projectRaw allocation m sigma w) := by
  refine ⟨fun hw sigma => completeKeep_project allocation m ε side w hw sigma, ?_⟩
  intro hw
  refine ⟨?_, ?_, ?_⟩
  · intro h a
    exact (hw h.val.physicalOrder).1 ⟨h, rfl⟩ a
  · intro h
    exact (hw h.val.physicalOrder).2.1 ⟨h, rfl⟩
  · intro i
    exact (hw i.1.val.physicalOrder).2.2 i rfl

def groupRawSource (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ)
    (sigma : Placement) : Tensor F
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) :=
  sourceTensor (groupCounts allocation m sigma)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => AllFieldHistoryRecovery.parents F h.val)

def groupPreparedSource (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ)
    (ε : ℝ) (sigma : Placement) : Tensor F
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) :=
  ExactRecovery.delete (groupRawSource F allocation m sigma)
    (completeKeep allocation m ε 0 sigma) (completeKeep allocation m ε 1 sigma)
    (completeKeep allocation m ε 2 sigma)

theorem rawSource_factor (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ)
    (x y z : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    AllFieldHistoryRecovery.rawSource F allocation m x y z =
      ∏ sigma : Placement, groupRawSource F allocation m sigma
        (projectRaw allocation m sigma x) (projectRaw allocation m sigma y)
        (projectRaw allocation m sigma z) :=
  prod_active_eq_prod_orders (fun h => ∏ j,
    AllFieldHistoryRecovery.parents F h (x h j) (y h j) (z h j))

theorem preparedSource_factor (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ)
    (x y z : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    ExactRecovery.delete (AllFieldHistoryRecovery.rawSource F allocation m)
      (AllFieldHistoryRecovery.completeKeep allocation m ε 0)
      (AllFieldHistoryRecovery.completeKeep allocation m ε 1)
      (AllFieldHistoryRecovery.completeKeep allocation m ε 2) x y z =
      ∏ sigma : Placement, groupPreparedSource F allocation m ε sigma
        (projectRaw allocation m sigma x) (projectRaw allocation m sigma y)
        (projectRaw allocation m sigma z) := by
  have heq :
      (AllFieldHistoryRecovery.completeKeep allocation m ε 0 x ∧
        AllFieldHistoryRecovery.completeKeep allocation m ε 1 y ∧
        AllFieldHistoryRecovery.completeKeep allocation m ε 2 z) ↔
      ∀ sigma : Placement,
        completeKeep allocation m ε 0 sigma (projectRaw allocation m sigma x) ∧
        completeKeep allocation m ε 1 sigma (projectRaw allocation m sigma y) ∧
        completeKeep allocation m ε 2 sigma (projectRaw allocation m sigma z) := by
    rw [completeKeep_iff_all_groups, completeKeep_iff_all_groups, completeKeep_iff_all_groups]
    exact ⟨fun h sigma => ⟨h.1 sigma, h.2.1 sigma, h.2.2 sigma⟩,
      fun h => ⟨fun sigma => (h sigma).1, fun sigma => (h sigma).2.1,
        fun sigma => (h sigma).2.2⟩⟩
  by_cases h : AllFieldHistoryRecovery.completeKeep allocation m ε 0 x ∧
      AllFieldHistoryRecovery.completeKeep allocation m ε 1 y ∧
      AllFieldHistoryRecovery.completeKeep allocation m ε 2 z
  · rw [ExactRecovery.delete, ite_eq_left h, rawSource_factor]
    apply Finset.prod_congr rfl
    intro sigma _
    exact (ite_eq_left (heq.mp h sigma)).symm
  · rw [ExactRecovery.delete, ite_eq_right h]
    have hn : ¬∀ sigma : Placement,
        completeKeep allocation m ε 0 sigma (projectRaw allocation m sigma x) ∧
        completeKeep allocation m ε 1 sigma (projectRaw allocation m sigma y) ∧
        completeKeep allocation m ε 2 sigma (projectRaw allocation m sigma z) :=
      fun hh => h (heq.mpr hh)
    obtain ⟨sigma, hs⟩ := not_forall.mp hn
    exact (Finset.prod_eq_zero (Finset.mem_univ sigma) (ite_eq_right hs)).symm

end MatrixMultiplication.AllFieldHistoryGroupMasks

end

end OAI
