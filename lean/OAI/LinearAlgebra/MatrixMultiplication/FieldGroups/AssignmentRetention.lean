import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.OrbitTransport
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.Admissible
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.AssignmentLoss

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupAssignmentRetention

open AllFieldHistory AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData JointCoarseHashing
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem good_local_failure_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (hg : (data allocation m ε sigma).Good k U N e s)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : Admissible allocation m ε sigma side e w) :
    (((localOrbit allocation m sigma e w).filter (fun v =>
      completeKeep allocation m ε (sigma side) sigma v ∧
        assigned allocation m ε sigma k U s (side, v) ≠ some (coarse allocation m sigma e))).card : ℝ) /
      ((localOrbit allocation m sigma e w).card : ℝ) ≤ 1 / N := by
  have ho : (side, orbitOf allocation m sigma e w) ∈ (data allocation m ε sigma).orbits e :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, rfl⟩
  have hh := good_failure_fraction_le allocation m ε sigma k U hAP N s e hg _ ho
  change (((passing allocation m sigma ε e (side, orbitOf allocation m sigma e w)).filter
      (fun v => assigned allocation m ε sigma k U s v ≠ some (coarse allocation m sigma e))).card : ℝ) /
    ((full allocation m sigma e (side, orbitOf allocation m sigma e w)).card : ℝ) ≤ 1 / N at hh
  rw [passing, Finset.filter_filter] at hh
  simp only [full_eq_tagged_localOrbit, Finset.filter_map, Finset.card_map] at hh
  rw [Finset.filter_congr_decidable] at hh
  exact hh

theorem localAssigned_iff (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (t : Triple (Pos (K := K) (tick := tick) allocation m sigma)) (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) :
    localAssigned allocation m sigma (physicalAssignment allocation m ε sigma k U s) t side w ↔
      assigned allocation m ε sigma k U s (sigma.symm side, w) = some t := by
  fin_cases side <;> rfl

theorem good_physical_local_failure_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (hg : (data allocation m ε sigma).Good k U N e s)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : Admissible allocation m ε sigma (sigma.symm side) e w) :
    (((localOrbit allocation m sigma e w).filter (fun v =>
      completeKeep allocation m ε side sigma v ∧
        ¬localAssigned allocation m sigma (physicalAssignment allocation m ε sigma k U s)
          (coarse allocation m sigma e) side v)).card : ℝ) /
      ((localOrbit allocation m sigma e w).card : ℝ) ≤ 1 / N := by
  simpa only [sigma.apply_symm_apply, localAssigned_iff] using
    good_local_failure_le allocation m ε sigma k U hAP N s e hg (sigma.symm side) w hw

theorem good_projected_failure_le (F : Type*) [CommRing F]
    (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m)
    (hg : (data allocation m ε sigma).Good k U N (projectTarget allocation m sigma e) s)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRecovery.Used F allocation m ε e side w) :
    (((localOrbit allocation m sigma (projectTarget allocation m sigma e)
      (projectRaw allocation m sigma w)).filter (fun v =>
        completeKeep allocation m ε side sigma v ∧
          ¬localAssigned allocation m sigma (physicalAssignment allocation m ε sigma k U s)
            (coarse allocation m sigma (projectTarget allocation m sigma e)) side v)).card : ℝ) /
      ((localOrbit allocation m sigma (projectTarget allocation m sigma e)
        (projectRaw allocation m sigma w)).card : ℝ) ≤ 1 / N := by
  apply good_physical_local_failure_le allocation m ε sigma k U hAP N s _ hg
  exact AllFieldGroupAdmissible.used_project_admissible F allocation m ε sigma e
    (sigma.symm side) w (by simpa only [sigma.apply_symm_apply] using hw)

end MatrixMultiplication.AllFieldGroupAssignmentRetention

end

end OAI
