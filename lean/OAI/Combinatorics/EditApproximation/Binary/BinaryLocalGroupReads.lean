import OAI.Combinatorics.EditApproximation.Binary.BinaryCellReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedLocalGroups

namespace OAI

/-! The physical query's outer whole-cell loops use the same dyadic
scales and exact Fin-count draws, with explicit initial-table lookups. -/

namespace EditApproximation
namespace BinaryFraction

section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

def preparedComputedCellReadWithWork (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let scales := groupScalesWithWork eM eb eF
  let result := preparedCellGroupReadWithWork source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
    R R hc hi scales.1 (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell
  (result.1, scales.2 + result.2 + 1)

theorem preparedComputedCellReadWithWork_eq (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hcurrent : ∀ i q, (current i q).2 ≤ R) :
    (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).1 =
    (preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF hM hb hF hP
      tau a (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) draw cell).1 := by
  have h := preparedCellGroupReadWithWork_eq source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
    R R hc hi (groupScalesWithWork eM eb eF).1
    (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell R R hp hcurrent
  simpa only [preparedComputedCellReadWithWork, preparedComputedCellGroupWithWork] using h

def preparedLocalGroupScaleReadWithWork (eb : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let b := 2 ^ eb
  let word := parentInitial query
  let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
  let radius := naturalCeilingWithWork word.1
  let cells := targetCellsWithWork side.1 (bitWordValue radius.1) query
  let selected := filterMapWithWork (fun cell =>
    preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb rfl
      (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (draw b cell)) cell) cells.1
  (selected.1, word.2 + side.2 + radius.2 + cells.2 + selected.2 + eb + 4)

theorem preparedLocalGroupScaleReadWithWork_eq (eb : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hcurrent : ∀ i q, (current i q).2 ≤ R) :
    (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).1 =
    (preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb hM hF hP tau a
      (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query).1 := by
  simp only [preparedLocalGroupScaleReadWithWork, preparedLocalGroupScaleWithWork,
    filterMapWithWork_value]
  apply List.filterMap_congr
  intro cell _
  have h := preparedComputedCellReadWithWork_eq source target parent P F exponent Q eM eF hM hF hP
    tau a parentInitial child initial current R hc hi (2 ^ eb) eb rfl
    (Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell))
    cell hp hcurrent
  simpa only using h

def preparedLocalCellGroupsReadWithWork (N : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let count := max 1 N.bits.length
  let word := parentInitial query
  let groups := arithmeticFlatMapWithWork (fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a word.1
    if guard.1 then
      let selected := preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF
        hM hF hP tau a parentInitial child initial current R hc hi eb draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)) (List.range count)
  (groups.1, word.2 + groups.2 + count + N.bits.length + 2)

theorem preparedLocalCellGroupsReadWithWork_eq (N : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hcurrent : ∀ i q, (current i q).2 ≤ R) :
    (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).1 =
    (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP tau a
      (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query).1 := by
  simp only [preparedLocalCellGroupsReadWithWork, preparedLocalCellGroupsWithWork,
    arithmeticFlatMapWithWork_value]
  apply List.flatMap_congr
  intro eb _
  split_ifs
  · have h := preparedLocalGroupScaleReadWithWork_eq source target parent P F exponent Q eM eF hM hF hP
      tau a parentInitial child initial current R hc hi eb draw query hp hcurrent
    simpa only using h
  · rfl

end Local
end BinaryFraction
end EditApproximation

end OAI
