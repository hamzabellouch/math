import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarBranchAnchors
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarActionUnique
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SparseStageIntervals
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarInactive

namespace OAI

/-! In an unused global slot a branch can only be at its source, at one
of its two parked endpoints, or at its final target. -/

noncomputable section

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting PlanarHamiltonian

theorem branchIndices_adjacent (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    (branchIndices M hM b 1).val = (branchIndices M hM b 0).val + 1 ∧
    (branchIndices M hM b 3).val = (branchIndices M hM b 2).val + 1 ∧
    (branchIndices M hM b 4).val = (branchIndices M hM b 3).val + 1 ∧
    (branchIndices M hM b 5).val = (branchIndices M hM b 4).val + 1 ∧
    (branchIndices M hM b 7).val = (branchIndices M hM b 6).val + 1 := by
  simp only [branchIndices, extractionIndex, scalingIndex, insertionIndex,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.val_mk]
  omega

theorem branch_unused_windows (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (i : ℕ)
    (hi : ∀ k, (branchIndices M hM b k).val ≠ i) :
    i ≤ (branchIndices M hM b 0).val ∨
      ((branchIndices M hM b 1).val + 1 ≤ i ∧ i ≤ (branchIndices M hM b 2).val) ∨
      ((branchIndices M hM b 5).val + 1 ≤ i ∧ i ≤ (branchIndices M hM b 6).val) ∨
      (branchIndices M hM b 7).val + 1 ≤ i := by
  have ha := branchIndices_adjacent M hM b
  have h₁ := hi 1
  have h₃ := hi 3
  have h₄ := hi 4
  have h₅ := hi 5
  have h₇ := hi 7
  omega

theorem sparseAnchor_source (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x : Plane) {i : ℕ}
    (hi : i ≤ (branchIndices M hM b 0).val) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i = x := by
  have hc := stagesBefore_before (branchIndices_strictMono M hM b) 0 rfl hi
  exact sparseAnchor_of_count _ _ _ 0 hc

theorem sparseAnchor_parkedSource (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x : Plane) {i : ℕ}
    (hlo : (branchIndices M hM b 1).val + 1 ≤ i)
    (hhi : i ≤ (branchIndices M hM b 2).val) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i =
      parkedSource (instruction M hM b) (parkingFor M hM b) x := by
  have hc := stagesBefore_between (branchIndices_strictMono M hM b) 1 2 rfl hlo hhi
  rw [sparseAnchor_of_count _ _ _ 2 hc]
  exact scaledStage_zero _ (parkingScale_pos _).ne' (by norm_num) _ _

theorem sparseAnchor_parkedTarget (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x : Plane) {i : ℕ}
    (hlo : (branchIndices M hM b 5).val + 1 ≤ i)
    (hhi : i ≤ (branchIndices M hM b 6).val) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i =
      (instruction M hM b).affine x +
        ((fun j => (parkingFor M hM b j : ℝ)) - (instruction M hM b).target.center) := by
  have hc := stagesBefore_between (branchIndices_strictMono M hM b) 5 6 rfl hlo hhi
  rw [sparseAnchor_of_count _ _ _ 6 hc]
  exact scaledStage_final _ (parkingScale_pos _).ne' (by norm_num) _ _

theorem sparseAnchor_target (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x : Plane) {i : ℕ}
    (hi : (branchIndices M hM b 7).val + 1 ≤ i) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i =
      (instruction M hM b).affine x := by
  have hc := stagesBefore_after (branchIndices_strictMono M hM b) 7 rfl hi
  exact sparseAnchor_of_count _ _ _ 8 hc

theorem parkedSource_mem (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) :
    parkedSource (instruction M hM b) (parkingFor M hM b) x ∈ (parkingRegion M hM b).carrier := by
  have h := (branchAnchors_mem_rectangle M hM b hx 2).1
  change scaledStage _ _ _ _ _ 0 ∈ _ at h
  rw [scaledStage_zero _ (parkingScale_pos _).ne' (by norm_num)] at h
  exact h

theorem parkedTarget_mem (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) :
    (instruction M hM b).affine x +
        ((fun j => (parkingFor M hM b j : ℝ)) - (instruction M hM b).target.center) ∈
      (parkingRegion M hM b).carrier := by
  have h := (branchAnchors_mem_rectangle M hM b hx 5).2
  change scaledStage _ _ _ _ _ 4 ∈ _ at h
  rw [scaledStage_final _ (parkingScale_pos _).ne' (by norm_num)] at h
  exact h

theorem ownPhase_surjective : Function.Surjective ownPhase := by
  intro p
  cases p with
  | extractHorizontal => exact ⟨0, rfl⟩
  | extractVertical => exact ⟨1, rfl⟩
  | scale k =>
      fin_cases k
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
  | insertVertical => exact ⟨6, rfl⟩
  | insertHorizontal => exact ⟨7, rfl⟩

theorem unused_owner_ne (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (i : Fin (actions M hM).length)
    (hi : ∀ k, (branchIndices M hM b k).val ≠ i.val) :
    ((actions M hM).get i).owner ≠ b := by
  intro he
  obtain ⟨k, hk⟩ := ownPhase_surjective ((actions M hM).get i).phase
  have hg : (actions M hM).get (branchIndices M hM b k) = (actions M hM).get i := by
    rw [branchIndices_get, hk]
    cases ha : (actions M hM).get i
    simp_all
  exact hi k (congrArg Fin.val ((List.nodup_iff_injective_get.mp (actions_nodup M hM)) hg))

end ForcedComputation.Recorder.Planar

end

end OAI
