import OAI.Combinatorics.EditApproximation.Geometry.LocalRefinementCones

namespace OAI

/-! The literal warmup can be calculated by direct bounded endpoint
loops. Equality with the complete tables is only asserted on good seeds;
the local rules themselves remain finite and bounded on every seed. -/

namespace EditApproximation

open Finset

def physicalLocalWarmup {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) : ℕ → PhysicalEntry M J target.length → ℚ
  | 0, state => stageInitial source target U N P F A state
  | t + 1, state =>
    if hbelow : state.1.1.val < J then
      if (physicalSourceInterval source.length state.1).hi -
          (physicalSourceInterval source.length state.1).lo ≤ 1 then
        stageInitial source target U N P F A state
      else rationalBellman (fun q => stageInitial source target U N P F A (state.1, q))
        (fun q r => targetEndpointDistance q r) (128 * F)
        (rationalActualWideActions (physicalSourceInterval source.length state.1)
          (localRefinementRepresentatives N P F (refinementFactor A F)
            (fun q => stageInitial source target U N P F A (state.1, q)) state.2) P)
        (fun is => physicalLocalWarmup source target U N P F A t
          (physicalChild state.1 hbelow is.1, is.2)) state.2
    else stageInitial source target U N P F A state

theorem physicalLocalWarmup_bounds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (t : ℕ) (state : PhysicalEntry M J target.length) :
    0 ≤ physicalLocalWarmup source target U N P F A t state ∧
      physicalLocalWarmup source target U N P F A t state ≤ stageInitial source target U N P F A state := by
  induction t generalizing state with
  | zero => exact ⟨stageInitial_nonneg_all_seeds source target U N P F A state, le_rfl⟩
  | succ t ih =>
    rw [physicalLocalWarmup]
    split_ifs
    · exact ⟨stageInitial_nonneg_all_seeds source target U N P F A state, le_rfl⟩
    · refine ⟨?_, rationalMinimum_le_fallback _ _⟩
      apply (le_rationalMinimum_iff _ _ _).2
      refine ⟨stageInitial_nonneg_all_seeds source target U N P F A state, ?_⟩
      intro v hv
      obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
      unfold rationalActionValue
      apply add_nonneg
      · exact add_nonneg (by positivity)
          (rationalActualWideActions_connection_nonneg _ _ _ action ha)
      · exact Finset.sum_nonneg (fun i _ => (ih _).1)
    · exact ⟨stageInitial_nonneg_all_seeds source target U N P F A state, le_rfl⟩

theorem physicalLocalWarmup_eq {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (t : ℕ) (state : PhysicalEntry M J target.length) :
    physicalLocalWarmup source target U N P F A t state =
      stageWarmup source target U N P F A t state := by
  induction t generalizing state with
  | zero => rfl
  | succ t ih =>
    change _ = rationalPhysicalBellman source target P (128 * F)
      (stageInitial source target U N P F A) (stageRepresentatives source target U N P F A)
      (stageWarmup source target U N P F A t) state
    rw [physicalLocalWarmup]
    unfold rationalPhysicalBellman
    dsimp only
    split_ifs
    · rfl
    · simp_rw [ih]
      exact physical_localRefinementBellman_eq source target U N P F A hsize hP hF hA hseed
        state.1 _ (fun is => stageWarmup_nonneg_all_seeds source target U N P F A t _) state.2
    · rfl

def physicalLocalWarmupMass {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (state : PhysicalEntry M J target.length) : ℚ :=
  (∑ t ∈ Finset.range T, physicalLocalWarmup source target U N P F A t state) / T

theorem physicalLocalWarmupMass_eq {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (state : PhysicalEntry M J target.length) :
    physicalLocalWarmupMass source target U N P F A T state =
      stageWarmupMass source target U N P F A T state := by
  unfold physicalLocalWarmupMass stageWarmupMass rationalPhysicalWarmupAverage
  simp_rw [physicalLocalWarmup_eq source target U N P F A hsize hP hF hA hseed]
  rfl

end EditApproximation

end OAI
