import OAI.Combinatorics.EditApproximation.Geometry.LocalGroupCones
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalQueryBudget

namespace OAI

/-! Bounded local cell loops on arbitrary initial seeds. -/

namespace EditApproximation

theorem localCellGroupActions_length {α : Type*} {M : ℕ} (source target : List α)
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (hF : 1 ≤ F) (hw : 0 ≤ parentInitial q) :
    (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q).length ≤
      (dyadicQueryWindow N (parentInitial q) a F).length *
        ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  unfold localCellGroupActions
  apply list_flatMap_length_le
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hbpos : 1 ≤ b := by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hb).1
    exact Nat.one_le_two_pow
  exact (List.length_filterMap_le _ _).trans
    (localTargetCells_query_length F b exponent q (parentInitial q) hF hbpos hw hwindow.1)

theorem localCellGroupActions_length_refinement {α : Type*} {M : ℕ} (source target : List α)
    (parent : TargetInterval source.length) (N P F exponent Q initialExponent : ℕ) (tau A : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (hF : 1 ≤ F) (hw : 0 ≤ parentInitial q)
    (hFbound : (F : ℚ) ≤ (2 : ℚ) ^ initialExponent)
    (hAbound : A ≤ (2 : ℚ) ^ initialExponent) :
    (localCellGroupActions source target parent N P F exponent Q tau (refinementFactor A F) parentInitial
      child initial current draw q).length ≤
      (initialExponent + 8) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  exact (localCellGroupActions_length source target parent N P F exponent Q tau (refinementFactor A F)
    parentInitial child initial current draw q hF hw).trans
    (Nat.mul_le_mul_right _ (refinement_query_window_length N F initialExponent A (parentInitial q)
      hF hFbound hAbound))

end EditApproximation

end OAI
