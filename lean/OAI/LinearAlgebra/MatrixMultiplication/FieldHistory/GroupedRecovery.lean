import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.GroupCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Recovery
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.GroupOrbitProjection
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.RecoveryOrbitDecisions

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupedRecovery

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem coordinates_project (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    GroupOrbitProjection.projectPair
      (ClassPositions (activeCounts allocation m))
      AllFieldHistoryMasks.Letters AllFieldHistoryMasks.Letters
      (fun h : Active K tick => h.val.physicalOrder = sigma)
      (AllFieldHistoryRecovery.coordinates allocation m e w) =
    groupCoordinates allocation m sigma (projectTarget allocation m sigma e)
      (projectRaw allocation m sigma w) := rfl

theorem idealSide_iff_all_groups (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    AllFieldHistoryRecovery.idealSide allocation m ε side e w ↔
      ∀ sigma, groupIdealSide allocation m ε side sigma
        (projectTarget allocation m sigma e) (projectRaw allocation m sigma w) := by
  constructor
  · intro hw sigma
    exact ⟨fun h j => hw.1 h.val j, fun h u hu => hw.2 h.val u hu⟩
  · intro hw
    exact ⟨fun h j => (hw h.val.physicalOrder).1 ⟨h, rfl⟩ j,
      fun h u hu => (hw h.val.physicalOrder).2 ⟨h, rfl⟩ u hu⟩

theorem project_joinGroupTargets (allocation : Allocation) (m : ℕ)
    (e : ∀ sigma, GroupTarget (K := K) (tick := tick) allocation m sigma)
    (sigma : Placement) :
    projectTarget allocation m sigma (joinGroupTargets (activeCounts allocation m) e) =
      e sigma := by
  funext h
  rcases h with ⟨h, hh⟩
  cases hh
  rfl

def groupedAssignment (allocation : Allocation) (m : ℕ) (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma)) :
    JointExtraction.Assignment (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
      (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
      (∀ sigma, E sigma) where
  x w := GroupAssignment.collect (fun sigma => (a sigma).x)
    (fun sigma => projectRaw allocation m sigma w)
  y w := GroupAssignment.collect (fun sigma => (a sigma).y)
    (fun sigma => projectRaw allocation m sigma w)
  z w := GroupAssignment.collect (fun sigma => (a sigma).z)
    (fun sigma => projectRaw allocation m sigma w)

theorem groupedAssignment_sound (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (i : ∀ sigma, E sigma) (e : ∀ sigma, GroupTarget (K := K) (tick := tick) allocation m sigma)
    (hx : ∀ sigma w, (a sigma).x w = some (i sigma) →
      groupIdealSide allocation m ε 0 sigma (e sigma) w)
    (hy : ∀ sigma w, (a sigma).y w = some (i sigma) →
      groupIdealSide allocation m ε 1 sigma (e sigma) w)
    (hz : ∀ sigma w, (a sigma).z w = some (i sigma) →
      groupIdealSide allocation m ε 2 sigma (e sigma) w) :
    (∀ w, (groupedAssignment allocation m E a).x w = some i →
      AllFieldHistoryRecovery.idealSide allocation m ε 0
        (joinGroupTargets (activeCounts allocation m) e) w) ∧
    (∀ w, (groupedAssignment allocation m E a).y w = some i →
      AllFieldHistoryRecovery.idealSide allocation m ε 1
        (joinGroupTargets (activeCounts allocation m) e) w) ∧
    (∀ w, (groupedAssignment allocation m E a).z w = some i →
      AllFieldHistoryRecovery.idealSide allocation m ε 2
        (joinGroupTargets (activeCounts allocation m) e) w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    apply (idealSide_iff_all_groups allocation m ε 0 _ w).2
    intro sigma
    rw [project_joinGroupTargets]
    exact hx sigma _ ((GroupAssignment.collect_eq_some _ _ _).mp hw sigma)
  · intro w hw
    apply (idealSide_iff_all_groups allocation m ε 1 _ w).2
    intro sigma
    rw [project_joinGroupTargets]
    exact hy sigma _ ((GroupAssignment.collect_eq_some _ _ _).mp hw sigma)
  · intro w hw
    apply (idealSide_iff_all_groups allocation m ε 2 _ w).2
    intro sigma
    rw [project_joinGroupTargets]
    exact hz sigma _ ((GroupAssignment.collect_eq_some _ _ _).mp hw sigma)

def localOrbit (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : GroupTarget (K := K) (tick := tick) allocation m sigma)
    (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Finset (GroupRaw (K := K) (tick := tick) allocation m sigma) :=
  GroupOrbitProjection.rawOrbit (groupCounts allocation m sigma)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => Fin (activeHalfLength h.val) → Fin 7) e w

def localAssigned (allocation : Allocation) (m : ℕ) (sigma : Placement) {E : Type*}
    (a : JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) E)
    (i : E) (side : Fin 3) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  AllFieldHistoryRecovery.sideVariable side (a.x w = some i) (a.y w = some i) (a.z w = some i)

theorem grouped_assigned_iff (allocation : Allocation) (m : ℕ)
    (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (i : ∀ sigma, E sigma) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    AllFieldHistoryRecovery.sideVariable side
      ((groupedAssignment allocation m E a).x w = some i)
      ((groupedAssignment allocation m E a).y w = some i)
      ((groupedAssignment allocation m E a).z w = some i) ↔
      ∀ sigma, localAssigned allocation m sigma (a sigma) (i sigma) side
        (projectRaw allocation m sigma w) := by
  fin_cases side <;> exact GroupAssignment.collect_eq_some _ _ _

theorem filter_eq_rejected {V : Type*} (orbit : Finset V)
    (bad : V → Prop) (d : DecidablePred bad) :
    @Finset.filter V bad d orbit = rejectedFilter orbit bad := by
  ext v
  simp only [rejectedFilter, Finset.mem_filter]

theorem grouped_collision_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (i : ∀ sigma, E sigma) (e : ∀ sigma, GroupTarget (K := K) (tick := tick) allocation m sigma)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hbound : ∀ sigma,
      (((localOrbit allocation m sigma (e sigma) (projectRaw allocation m sigma w)).filter
        (fun v => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma v ∧
          ¬localAssigned allocation m sigma (a sigma) (i sigma) side v)).card : ℝ) /
        (localOrbit allocation m sigma (e sigma) (projectRaw allocation m sigma w)).card ≤ 1 / m) :
    letI : MulAction (AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m)
      (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :=
        AllFieldHistoryRecovery.rawAction allocation m (joinGroupTargets (activeCounts allocation m) e)
    (((OrbitCounting.orbitSet (G := AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => AllFieldHistoryRecovery.completeKeep allocation m ε side v ∧
        ¬AllFieldHistoryRecovery.sideVariable side
          ((groupedAssignment allocation m E a).x v = some i)
          ((groupedAssignment allocation m E a).y v = some i)
          ((groupedAssignment allocation m E a).z v = some i))).card : ℝ) /
      (OrbitCounting.orbitSet (G := AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m) w).card ≤ 6 / m := by
  let target := joinGroupTargets (activeCounts allocation m) e
  let : MulAction (AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m)
      (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) := AllFieldHistoryRecovery.rawAction allocation m target
  have hb (sigma : Placement) :
      ((rejectedFilter (GroupOrbitProjection.rawOrbit
        (GroupOrbitProjection.groupCounts (activeCounts allocation m)
          (fun h : Active K tick => h.val.physicalOrder = sigma))
        (fun h => Left activeHalfLength h.val) (fun h => Right activeHalfLength h.val)
        (GroupOrbitProjection.projectTarget (activeCounts allocation m)
          (fun h => h.val.physicalOrder = sigma) target)
        (projectRaw allocation m sigma w))
        (fun v => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma v ∧
          ¬localAssigned allocation m sigma (a sigma) (i sigma) side v)).card : ℝ) /
        (GroupOrbitProjection.rawOrbit
          (GroupOrbitProjection.groupCounts (activeCounts allocation m)
            (fun h : Active K tick => h.val.physicalOrder = sigma))
          (fun h => Left activeHalfLength h.val) (fun h => Right activeHalfLength h.val)
          (GroupOrbitProjection.projectTarget (activeCounts allocation m)
            (fun h => h.val.physicalOrder = sigma) target)
          (projectRaw allocation m sigma w)).card ≤ 1 / m := by
    change ((rejectedFilter
      (localOrbit allocation m sigma (projectTarget allocation m sigma target)
        (projectRaw allocation m sigma w))
      (fun v => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma v ∧
        ¬localAssigned allocation m sigma (a sigma) (i sigma) side v)).card : ℝ) /
      (localOrbit allocation m sigma (projectTarget allocation m sigma target)
        (projectRaw allocation m sigma w)).card ≤ 1 / m
    dsimp only [target]
    rw [project_joinGroupTargets]
    have hb0 := hbound sigma
    rw [filter_eq_rejected] at hb0
    exact hb0
  have hh := GroupOrbitProjection.raw_group_passing_rejection_fraction_le
    (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
    (fun h : Active K tick => h.val.physicalOrder) target w
    (AllFieldHistoryRecovery.completeKeep allocation m ε side)
    (fun sigma => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma)
    (fun sigma => localAssigned allocation m sigma (a sigma) (i sigma) side)
    (fun v hv sigma => completeKeep_project allocation m ε side v hv sigma)
    (fun _ => (1 : ℝ) / m) hb
  have hcard : Fintype.card Placement = 6 := by
    norm_num [Placement, Fintype.card_perm, Nat.factorial]
  have horbit :
      OrbitCounting.orbitSet
        (G := AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m) w =
      GroupOrbitProjection.rawOrbit (activeCounts allocation m)
        (Left activeHalfLength) (Right activeHalfLength) target w := by
    exact RecoveryOrbitDecisions.orbitSet_eq_transportedOrbit
      (G := AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m)
      _ _ _ (AllFieldHistoryRecovery.coordinates allocation m target) w
  rw [filter_eq_rejected, horbit]
  have hfilter := rejectedFilter_congr
    (GroupOrbitProjection.rawOrbit (activeCounts allocation m)
      (Left activeHalfLength) (Right activeHalfLength) target w)
    (fun v => AllFieldHistoryRecovery.completeKeep allocation m ε side v ∧
      ¬AllFieldHistoryRecovery.sideVariable side
        ((groupedAssignment allocation m E a).x v = some i)
        ((groupedAssignment allocation m E a).y v = some i)
        ((groupedAssignment allocation m E a).z v = some i))
    (fun v => AllFieldHistoryRecovery.completeKeep allocation m ε side v ∧
      ¬∀ sigma, localAssigned allocation m sigma (a sigma) (i sigma) side
        (GroupOrbitProjection.projectRaw (activeCounts allocation m)
          (Left activeHalfLength) (Right activeHalfLength)
          (fun h : Active K tick => h.val.physicalOrder = sigma) v))
    (fun v => and_congr Iff.rfl
      (not_congr (grouped_assigned_iff allocation m E a i side v)))
  rw [hfilter]
  simpa only [Finset.sum_const, Finset.card_univ,
    hcard, nsmul_eq_mul, Nat.cast_ofNat, mul_one_div] using hh

theorem repair_grouped (F : Type*) [CommRing F] (allocation : Allocation)
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (i : ∀ sigma, E sigma) (e : ∀ sigma, GroupTarget (K := K) (tick := tick) allocation m sigma)
    (hx : ∀ sigma w, (a sigma).x w = some (i sigma) →
      groupIdealSide allocation m ε 0 sigma (e sigma) w)
    (hy : ∀ sigma w, (a sigma).y w = some (i sigma) →
      groupIdealSide allocation m ε 1 sigma (e sigma) w)
    (hz : ∀ sigma w, (a sigma).z w = some (i sigma) →
      groupIdealSide allocation m ε 2 sigma (e sigma) w)
    (hbound : ∀ side w,
      AllFieldHistoryRecovery.Used F allocation m ε
        (joinGroupTargets (activeCounts allocation m) e) side w → ∀ sigma,
      (((localOrbit allocation m sigma (e sigma) (projectRaw allocation m sigma w)).filter
        (fun v => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma v ∧
          ¬localAssigned allocation m sigma (a sigma) (i sigma) side v)).card : ℝ) /
        (localOrbit allocation m sigma (e sigma) (projectRaw allocation m sigma w)).card ≤ 1 / m) :
    InverseLinearRecovery.RecoveredBy
      (AllFieldHistoryRecovery.ideal F allocation m ε (joinGroupTargets (activeCounts allocation m) e))
      (JointExtraction.branch
        (ExactRecovery.delete (AllFieldHistoryRecovery.rawSource F allocation m)
          (AllFieldHistoryRecovery.completeKeep allocation m ε 0)
          (AllFieldHistoryRecovery.completeKeep allocation m ε 1)
          (AllFieldHistoryRecovery.completeKeep allocation m ε 2))
        (groupedAssignment allocation m E a) i)
      (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m) := by
  have hs := groupedAssignment_sound allocation m ε E a i e hx hy hz
  apply AllFieldHistoryRecovery.repair_selected_branch F allocation hε hm
    (groupedAssignment allocation m E a) i (joinGroupTargets (activeCounts allocation m) e)
    hs.1 hs.2.1 hs.2.2
  intro side w hw
  exact grouped_collision_le allocation m ε E a i e side w (hbound side w hw)

end MatrixMultiplication.AllFieldHistoryGroupedRecovery

end

end OAI
