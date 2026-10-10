import OAI.Combinatorics.EditApproximation.Refinement.PhysicalWarmup
import OAI.Combinatorics.EditApproximation.Geometry.LocalInitialCones
import OAI.Combinatorics.EditApproximation.Geometry.Leaves
import OAI.Combinatorics.EditApproximation.Probability.Exact
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The actual initial table uses exact empty/singleton leaves and local cones elsewhere. -/

namespace EditApproximation

open EditDistortion



theorem shortSourceCost_eq_edit {α : Type*} [DecidableEq α] (source target : List α)
    (hsource : source.length ≤ 1) : shortSourceCost source target = edit source target := by
  cases source with
  | nil =>
    exact (edit_nil_left target).symm
  | cons a rest =>
    have hrest : rest = [] := List.length_eq_zero_iff.mp (by
      simp only [List.length_cons] at hsource
      omega)
    subst rest
    exact singletonCost_eq_edit a target

def physicalInitialTable {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (state : PhysicalEntry M J target.length) : ℚ :=
  let piece := physicalSource source state.1
  if piece.length ≤ 1 then shortSourceCost piece (substring target state.2.lo state.2.hi)
  else localInitialConeTable piece target (fun q => U (state.1, q)) N P F A a state.2

theorem physicalSource_length_le {α : Type*} {M J : ℕ} (source : List α)
    (node : PhysicalNode M J) : (physicalSource source node).length ≤ source.length := by
  simp only [physicalSource, substring, List.length_drop, List.length_take]
  exact (Nat.sub_le _ _).trans (min_le_right _ _)

theorem physical_state_cost_le {α : Type*} {M J : ℕ} (source target : List α)
    (N : ℕ) (hsize : source.length + target.length ≤ N)
    (state : PhysicalEntry M J target.length) :
    stateEditCost (physicalSource source state.1) target state.2 ≤ N := by
  apply (edit_le_max_length _ _).trans
  apply max_le
  · exact (physicalSource_length_le source state.1).trans (by omega)
  · have hlen : (substring target state.2.lo state.2.hi).length ≤ target.length := by
      simp only [substring, List.length_drop, List.length_take]
      exact (Nat.sub_le _ _).trans (min_le_right _ _)
    exact hlen.trans (by omega)

theorem physicalInitialTable_bounds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A a : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A) (ha : 1 ≤ a) (hfactor : A ≤ a * F)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (state : PhysicalEntry M J target.length) :
    max ((stateEditCost (physicalSource source state.1) target state.2 : ℚ) / a)
        |rationalStateGap (physicalSource source state.1) target state.2| ≤
      physicalInitialTable source target U N P F A a state ∧
    physicalInitialTable source target U N P F A a state ≤
      2 * F * stateEditCost (physicalSource source state.1) target state.2 := by
  unfold physicalInitialTable
  dsimp only
  split_ifs with hleaf
  · rw [shortSourceCost_eq_edit _ _ hleaf]
    change max ((stateEditCost _ _ _ : ℚ) / a) |rationalStateGap _ _ _| ≤
        stateEditCost _ _ _ ∧ (stateEditCost _ _ _ : ℚ) ≤ 2 * F * stateEditCost _ _ _
    have hc : (0 : ℚ) ≤ stateEditCost (physicalSource source state.1) target state.2 := Nat.cast_nonneg _
    have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
    have hgap := stateEditCost_length_lower (physicalSource source state.1) target state.2
    rw [← rationalStateGap_cast] at hgap
    constructor
    · apply max_le
      · apply (div_le_iff₀ (by linarith : 0 < a)).2
        nlinarith
      · exact_mod_cast hgap
    · nlinarith
  · rw [localInitialConeTable_eq_global _ _ _ N P F A a hP hF hA ha hfactor
      (fun q => physical_state_cost_le source target N hsize (state.1, q))
      (fun q => hseed (state.1, q))]
    exact globalInitialConeTable_bounds _ _ _ N P F A a hP hF hA ha hfactor
      (fun q => physical_state_cost_le source target N hsize (state.1, q))
      (fun q => hseed (state.1, q)) state.2

theorem physicalInitialTable_real_lower {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A a : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A) (ha : 1 ≤ a) (hfactor : A ≤ a * F)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2) :
    physicalLower source target (a : ℝ) ≤
      fun state => (physicalInitialTable source target U N P F A a state : ℝ) := by
  intro state
  have h := (physicalInitialTable_bounds source target U N P F A a hsize hP hF hA ha hfactor hseed state).1
  have hR : ((max ((stateEditCost (physicalSource source state.1) target state.2 : ℚ) / a)
      |rationalStateGap (physicalSource source state.1) target state.2| : ℚ) : ℝ) ≤
      (physicalInitialTable source target U N P F A a state : ℝ) := Rat.cast_le.mpr h
  simpa only [Rat.cast_max, Rat.cast_div, Rat.cast_natCast, Rat.cast_abs,
    rationalStateGap_cast, physicalLower] using hR

end EditApproximation

end OAI
