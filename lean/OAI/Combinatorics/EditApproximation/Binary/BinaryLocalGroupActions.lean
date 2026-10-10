import OAI.Combinatorics.EditApproximation.Binary.BinaryComputedCellGroup
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The complete local group list is obtained by executed scale, cell,
band, and sampled-selection loops. The source keeps the original finite
sample counts and shares its draws between all members of each cell. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem refinementScaleGuardWithWork_value (F b : ℕ) (a w : BinaryFraction) :
    (refinementScaleGuardWithWork F b a w).1 = true ↔
      w.value / (16 * F) ≤ b ∧ (b : ℚ) ≤ 8 * a.value * w.value := by
  simp only [refinementScaleGuardWithWork, Bool.and_eq_true, leWithWork_value,
    canonicalMulWithWork_value, divWithWork_value, nat_value, Nat.cast_ofNat]

private theorem cellDraw_roundtrip (M b Q : ℕ) (f g : ℚ) (h : f = g)
    (draw : cellScaleDraw M b Q g) :
    Eq.mp (congrArg (cellScaleDraw M b Q) h)
      (Eq.mpr (congrArg (cellScaleDraw M b Q) h) draw) = draw := by
  cases h
  rfl

def localGroupScaleWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent Q eM eF eb : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let b := 2 ^ eb
  let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
  let radius := naturalCeilingWithWork (parentInitial query)
  let cells := targetCellsWithWork side.1 (bitWordValue radius.1) query
  let selected := filterMapWithWork (fun cell =>
    computedCellGroupWithWork source target parent b P F exponent Q eM eb eF hM rfl hF
      tau a parentInitial child initial current
      (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (draw b cell)) cell) cells.1
  (selected.1, side.2 + radius.2 + cells.2 + selected.2 + eb + 4)

theorem localGroupScaleWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent Q eM eF eb : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) (hP : 0 < P) :
    ((localGroupScaleWithWork source target parent P F exponent Q eM eF eb hM hF tau a
      parentInitial child initial current draw query).1.map BinaryBellmanAction.decode) =
      (localTargetCells (((2 : ℚ) ^ (-(exponent : ℤ))) * (2 ^ eb : ℕ))
        ⌈(parentInitial query).value⌉₊ query).filterMap (fun cell =>
        chooseCellGroupAction source target parent (2 ^ eb) P F exponent Q tau.value a.value
          (fun r => (parentInitial r).value) (fun i r => (child i r).value)
          (fun i r => (initial i r).value) (fun i r => (current i r).value) cell (draw (2 ^ eb) cell)) := by
  simp only [localGroupScaleWithWork, filterMapWithWork_value, List.map_filterMap,
    targetCellsWithWork_value, canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
    naturalCeilingWithWork_value]
  apply List.filterMap_congr
  intro cell _
  have hv := computedCellGroupWithWork_value source target parent (2 ^ eb) P F exponent Q eM eb eF
      hM rfl hF tau a parentInitial child initial current
      (Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell)) cell hP
  rw [cellDraw_roundtrip M (2 ^ eb) Q (nat F).value (F : ℚ) (nat_value F)
    (draw (2 ^ eb) cell)] at hv
  exact hv

def localCellGroupsWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let count := max 1 N.bits.length
  let groups := arithmeticFlatMapWithWork (fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)
    if guard.1 then
      let selected := localGroupScaleWithWork source target parent P F exponent Q eM eF eb hM hF
        tau a parentInitial child initial current draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)) (List.range count)
  (groups.1, groups.2 + count + N.bits.length + 2)

private theorem flatMap_filter_condition {α β : Type*} (p : α → Bool) (f : α → List β)
    (xs : List α) :
    xs.flatMap (fun x => if p x then f x else []) = (xs.filter p).flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.filter_cons]
    cases p x <;> simp only [Bool.false_eq_true, ↓reduceIte, List.flatMap_cons,
      List.nil_append, ih]

theorem localCellGroupsWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) (hP : 0 < P) :
    ((localCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF tau a
      parentInitial child initial current draw query).1.map BinaryBellmanAction.decode) =
      localCellGroupActions source target parent N P F exponent Q tau.value a.value
        (fun r => (parentInitial r).value) (fun i r => (child i r).value)
        (fun i r => (initial i r).value) (fun i r => (current i r).value) draw query := by
  let predicate := fun b : ℕ => decide ((parentInitial query).value / (16 * (F : ℚ)) ≤ b ∧
    (b : ℚ) ≤ 8 * a.value * (parentInitial query).value)
  let values := fun b : ℕ => (localTargetCells (((2 : ℚ) ^ (-(exponent : ℤ))) * b)
    ⌈(parentInitial query).value⌉₊ query).filterMap (fun cell =>
      chooseCellGroupAction source target parent b P F exponent Q tau.value a.value
        (fun r => (parentInitial r).value) (fun i r => (child i r).value)
        (fun i r => (initial i r).value) (fun i r => (current i r).value) cell (draw b cell))
  have hscale : (List.range (max 1 N.bits.length)).map (fun eb => 2 ^ eb) = dyadicScales N := by
    simpa only [dyadicScalesWithWork, arithmeticMapWithWork_value, powerTwoWord_value] using
      dyadicScalesWithWork_value N
  have hguard (eb : ℕ) : (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)).1 =
      predicate (2 ^ eb) := Bool.eq_iff_iff.mpr (by
        simp only [refinementScaleGuardWithWork_value, predicate, decide_eq_true_eq])
  unfold localCellGroupsWithWork
  simp only [arithmeticFlatMapWithWork_value, List.map_flatMap]
  trans (List.range (max 1 N.bits.length)).flatMap
    (fun eb => if predicate (2 ^ eb) then values (2 ^ eb) else [])
  · apply List.flatMap_congr
    intro eb _
    by_cases hg : (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)).1 = true
    · have hp : predicate (2 ^ eb) = true := (hguard eb) ▸ hg
      simp only [ite_eq_left hg, ite_eq_left hp]
      exact localGroupScaleWithWork_value source target parent P F exponent Q eM eF eb hM hF
        tau a parentInitial child initial current draw query hP
    · have hp : predicate (2 ^ eb) ≠ true := by simpa only [← hguard eb] using hg
      simp only [ite_eq_right hg, ite_eq_right hp, List.map_nil]
  · calc
      _ = ((List.range (max 1 N.bits.length)).map (fun eb => 2 ^ eb)).flatMap
          (fun b => if predicate b then values b else []) :=
        (List.flatMap_map _ _ _).symm
      _ = (((List.range (max 1 N.bits.length)).map (fun eb => 2 ^ eb)).filter predicate).flatMap
          values := flatMap_filter_condition _ _ _
      _ = _ := by rw [hscale]; rfl

end BinaryFraction
end EditApproximation

end OAI
