import OAI.Combinatorics.EditApproximation.Refinement.PhysicalInitial
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRationalWarmup
import OAI.Combinatorics.EditApproximation.Geometry.ActualRepresentatives
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The literal initial table, representative enumeration and rational warmup of one refinement pass. -/

namespace EditApproximation



theorem refinementFactor_spec (A : ℚ) (F : ℕ) (hF : 0 < F) :
    1 ≤ refinementFactor A F ∧ A ≤ refinementFactor A F * F := by
  have hFr : (0 : ℚ) < F := by exact_mod_cast hF
  refine ⟨le_max_left _ _, ?_⟩
  have h := mul_le_mul_of_nonneg_right (le_max_right (1 : ℚ) (A / F)) hFr.le
  rw [div_mul_cancel₀ _ hFr.ne'] at h
  exact h

def stageInitial {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) :
    PhysicalEntry M J target.length → ℚ :=
  physicalInitialTable source target U N P F A (refinementFactor A F)

def stageRepresentatives {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
    (node : PhysicalNode M J) : List (ℕ × TargetInterval target.length) :=
  representativeList N P F (refinementFactor A F) (fun q => stageInitial source target U N P F A (node, q))

def stageWarmup {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) :
    ℕ → PhysicalEntry M J target.length → ℚ :=
  rationalPhysicalWarmup source target P (128 * F) (stageInitial source target U N P F A)
    (stageRepresentatives source target U N P F A)

def stageWarmupMass {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) :
    PhysicalEntry M J target.length → ℚ :=
  rationalPhysicalWarmupAverage source target P (128 * F) (stageInitial source target U N P F A)
    (stageRepresentatives source target U N P F A) T

theorem stageWarmup_invariants {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (state : PhysicalEntry M J target.length) :
    physicalLower source target (refinementFactor A F : ℝ) state ≤
        (stageWarmup source target U N P F A T state : ℝ) ∧
      stageWarmup source target U N P F A T state ≤ stageWarmupMass source target U N P F A T state ∧
      stageWarmupMass source target U N P F A T state ≤ stageInitial source target U N P F A state ∧
      stageInitial source target U N P F A state ≤
        2 * F * stateEditCost (physicalSource source state.1) target state.2 := by
  have hfactor := refinementFactor_spec A F (by omega)
  have hinit := physicalInitialTable_real_lower source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed
  have haR : (1 : ℝ) ≤ refinementFactor A F := by exact_mod_cast hfactor.1
  have hLR : (1 : ℝ) ≤ (128 * F : ℚ) := by
    have hFr : (1 : ℚ) ≤ F := by exact_mod_cast hF
    exact_mod_cast (show (1 : ℚ) ≤ 128 * F by linarith)
  have hlower := physicalWarmup_lower source target hM P (refinementFactor A F : ℝ)
    ((128 * F : ℚ) : ℝ) haR hLR
    (fun s => (stageInitial source target U N P F A s : ℝ))
    (stageRepresentatives source target U N P F A) hinit T state
  have hsandwich := physicalWarmup_average_sandwich source target P ((128 * F : ℚ) : ℝ)
    (fun s => (stageInitial source target U N P F A s : ℝ))
    (stageRepresentatives source target U N P F A) T hT state
  have hupper := (physicalInitialTable_bounds source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed state).2
  refine ⟨?_, ?_, ?_, hupper⟩
  · simpa only [stageWarmup, rationalPhysicalWarmup_cast] using hlower
  · have h := hsandwich.1
    rw [← rationalPhysicalWarmup_cast, ← rationalPhysicalWarmupAverage_cast] at h
    exact Rat.cast_le.mp h
  · have h := hsandwich.2
    rw [← rationalPhysicalWarmupAverage_cast] at h
    exact Rat.cast_le.mp h

end EditApproximation

end OAI
