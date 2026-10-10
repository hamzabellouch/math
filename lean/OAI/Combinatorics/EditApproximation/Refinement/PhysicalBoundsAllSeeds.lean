import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementInvariants

namespace OAI

/-! Nonnegativity and size bounds hold on every seed and every sample outcome. -/

namespace EditApproximation

open Finset

theorem rationalActualWideActions_connection_nonneg {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (action : PhysicalRationalAction M ny)
    (ha : action ∈ rationalActualWideActions parent representatives P) : 0 ≤ action.connection := by
  obtain ⟨br, _, hmem⟩ := List.mem_flatMap.mp ha
  obtain ⟨states, _, rfl⟩ := List.mem_map.mp hmem
  exact Nat.cast_nonneg _

theorem localInitialConeTable_nonneg {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ) (q : TargetInterval target.length) :
    0 ≤ localInitialConeTable source target U N P F A a q := by
  unfold localInitialConeTable
  split_ifs
  · exact le_rfl
  · apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨by positivity, ?_⟩
    intro v hv
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
    unfold initialConeValue scaledSeedValue
    positivity

 theorem stageInitial_nonneg_all_seeds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (state : PhysicalEntry M J target.length) :
    0 ≤ stageInitial source target U N P F A state := by
  unfold stageInitial physicalInitialTable
  dsimp only
  split_ifs
  · exact Nat.cast_nonneg _
  · exact localInitialConeTable_nonneg _ _ _ _ _ _ _ _ _

 theorem stageInitial_upper_all_seeds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (state : PhysicalEntry M J target.length) :
    stageInitial source target U N P F A state ≤ (32 * F + 1 : ℚ) * N := by
  unfold stageInitial physicalInitialTable
  dsimp only
  split_ifs with hleaf
  · rw [shortSourceCost_eq_edit _ _ hleaf]
    have hcost : (stateEditCost (physicalSource source state.1) target state.2 : ℚ) ≤ N := by
      exact_mod_cast physical_state_cost_le source target N hsize state
    change (stateEditCost (physicalSource source state.1) target state.2 : ℚ) ≤ _
    have hcoef : (1 : ℚ) ≤ 32 * F + 1 := by
      have hF : (0 : ℚ) ≤ F := Nat.cast_nonneg _
      linarith
    exact hcost.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℚ) N))
  · unfold localInitialConeTable
    split_ifs
    · positivity
    · exact rationalMinimum_le_fallback _ _

 theorem rationalPhysicalBellman_nonneg {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (hL : 0 ≤ L) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (hinitial : ∀ state, 0 ≤ initial state)
    (value : PhysicalEntry M J target.length → ℚ) (hvalue : ∀ state, 0 ≤ value state)
    (state : PhysicalEntry M J target.length) :
    0 ≤ rationalPhysicalBellman source target P L initial representatives value state := by
  unfold rationalPhysicalBellman
  dsimp only
  split_ifs
  · exact hinitial state
  · apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨hinitial state, ?_⟩
    intro v hv
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
    unfold rationalActionValue
    exact add_nonneg (add_nonneg (mul_nonneg hL (Nat.cast_nonneg _))
      (rationalActualWideActions_connection_nonneg _ _ _ action ha)) (sum_nonneg fun i _ => hvalue _)
  · exact hinitial state

 theorem stageWarmup_nonneg_all_seeds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (t : ℕ) (state : PhysicalEntry M J target.length) :
    0 ≤ stageWarmup source target U N P F A t state := by
  induction t generalizing state with
  | zero => exact stageInitial_nonneg_all_seeds source target U N P F A state
  | succ t ih =>
    exact rationalPhysicalBellman_nonneg source target P (128 * F) (by positivity) _ _
      (stageInitial_nonneg_all_seeds source target U N P F A) _ ih state

 theorem stageWarmup_le_initial_all_seeds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (t : ℕ) (state : PhysicalEntry M J target.length) :
    stageWarmup source target U N P F A t state ≤ stageInitial source target U N P F A state := by
  cases t with
  | zero => exact le_rfl
  | succ t =>
    change rationalPhysicalBellman source target P (128 * F) _ _ _ state ≤ _
    unfold rationalPhysicalBellman
    dsimp only
    split_ifs
    · exact le_rfl
    · exact rationalMinimum_le_fallback _ _
    · exact le_rfl

 theorem physicalRefinement_upper_all_seeds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q ≤ (32 * F + 1 : ℚ) * N := by
  exact (physicalRefinement_le_warmup source target U N P F A T delta choices node t q).trans
    ((stageWarmup_le_initial_all_seeds source target U N P F A T (node, q)).trans
      (stageInitial_upper_all_seeds source target U N P F A hsize (node, q)))

 theorem physicalRefinement_nonneg_all_seeds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length) :
    0 ≤ physicalRefinement source target U N P F A T delta choices node t q := by
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · rw [physicalRefinement_at_terminal source target U N P F A T delta choices node (Or.inr hleaf)]
      exact stageInitial_nonneg_all_seeds source target U N P F A (node, q)
    · have hpost := (physicalRefinement_bellman_invariants source target U N P F A T delta choices node t q).1
      have hnonneg : 0 ≤ rationalPhysicalBellman source target P (128 * F)
          (stageInitial source target U N P F A) (stageRepresentatives source target U N P F A)
          (fun state => physicalRefinement source target U N P F A T delta choices state.1 t state.2) (node, q) := by
        unfold rationalPhysicalBellman
        dsimp only
        rw [dite_eq_left hbelow, ite_eq_right hleaf]
        apply (le_rationalMinimum_iff _ _ _).2
        refine ⟨stageInitial_nonneg_all_seeds source target U N P F A (node, q), ?_⟩
        intro v hv
        obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
        unfold rationalActionValue
        apply add_nonneg
        · exact add_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
            (rationalActualWideActions_connection_nonneg _ _ _ action ha)
        · apply sum_nonneg
          intro i _
          exact physicalRefinement_nonneg_all_seeds source target U N P F A T delta choices
            (physicalChild node hbelow (action.childState i).1) t (action.childState i).2
      exact hnonneg.trans hpost
  · rw [physicalRefinement_at_terminal source target U N P F A T delta choices node (Or.inl hbelow)]
    exact stageInitial_nonneg_all_seeds source target U N P F A (node, q)
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

end EditApproximation

end OAI
