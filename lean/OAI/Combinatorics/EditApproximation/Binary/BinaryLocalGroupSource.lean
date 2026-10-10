import OAI.Combinatorics.EditApproximation.Binary.BinaryCellSourcePort
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGroupReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryReadCostBounds
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation





private theorem cellScaleReadDraw_cast_plain (M b Q : ℕ) (f g : ℚ) (h : f = g)
    (draw : cellScaleReadDraw M b Q g) :
    (fun t i => ((Eq.mpr (congrArg (cellScaleReadDraw M b Q) h) draw) t i).1) =
      Eq.mpr (congrArg (BinaryFraction.cellScaleDraw M b Q) h) (fun t i => (draw t i).1) := by
  cases h
  rfl

private theorem cellScaleReadDraw_cast_bound (M b Q : ℕ) (f g : ℚ) (h : f = g)
    (draw : cellScaleReadDraw M b Q g) (S : ℕ) (hs : ∀ t i, (draw t i).2 ≤ S) :
    ∀ t i, ((Eq.mpr (congrArg (cellScaleReadDraw M b Q) h) draw) t i).2 ≤ S := by
  cases h
  exact hs

namespace BinaryFraction
section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

def preparedComputedCellSourceWithWork (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M × ℕ)
    (cell : ℕ × ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let scales := groupScalesWithWork eM eb eF
  let result := preparedCellGroupSourceWithWork source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
    R R hc hi scales.1 (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell
  (result.1, scales.2 + result.2 + 1)

theorem preparedComputedCellSourceWithWork_eq_cost (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M × ℕ)
    (cell : ℕ × ℕ) (S : ℕ) (hs : ∀ t i, (draw t i).2 ≤ S) :
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).1 =
      (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb hb (fun t i => (draw t i).1) cell).1 ∧
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).2 ≤
      (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb hb (fun t i => (draw t i).1) cell).2 * (S + 4) := by
  have h := preparedCellGroupSourceWithWork_eq_cost source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current R R hc hi
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF)
    draw cell S hs
  unfold preparedComputedCellSourceWithWork preparedComputedCellReadWithWork
  dsimp only
  rw [h.1]
  exact ⟨rfl, by nlinarith only [h.2]⟩

private theorem add_source_cost (u v read plain S : ℕ) (h : read ≤ plain * (S + 4)) :
    u + read + v ≤ (u + plain + v) * (S + 4) := by
  have hconst : u + v ≤ (u + v) * (S + 4) :=
    Nat.le_mul_of_pos_right _ (by omega)
  calc
    u + read + v ≤ u + plain * (S + 4) + v := by omega
    _ = plain * (S + 4) + (u + v) := by omega
    _ ≤ plain * (S + 4) + (u + v) * (S + 4) := Nat.add_le_add_left hconst _
    _ = (u + plain + v) * (S + 4) := by ring

private theorem computedCellSource_cast_cost (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleReadDraw M b Q F) (cell : ℕ × ℕ) (S : ℕ)
    (hs : ∀ t i, (draw t i).2 ≤ S) :
    let castDraw := Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) draw
    let plainDraw := Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (fun t i => (draw t i).1)
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb castDraw cell).1 =
      (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb hb plainDraw cell).1 ∧
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb castDraw cell).2 ≤
      (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb hb plainDraw cell).2 * (S + 4) := by
  dsimp only
  have h := preparedComputedCellSourceWithWork_eq_cost source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial current R hc hi b eb hb
    (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) draw) cell S
    (cellScaleReadDraw_cast_bound M b Q _ _ (nat_value F) draw S hs)
  rw [cellScaleReadDraw_cast_plain M b Q _ _ (nat_value F) draw] at h
  exact h

def preparedLocalGroupScaleSourceWithWork (eb : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let b := 2 ^ eb
  let word := parentInitial query
  let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
  let radius := naturalCeilingWithWork word.1
  let cells := targetCellsWithWork side.1 (bitWordValue radius.1) query
  let selected := filterMapWithWork (fun cell =>
    preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb rfl
      (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell)) cell) cells.1
  (selected.1, word.2 + side.2 + radius.2 + cells.2 + selected.2 + eb + 4)

theorem preparedLocalGroupScaleSourceWithWork_eq_cost_on (eb : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length)
    (S : ℕ) (hs : ∀ cell ∈ (targetCellsWithWork
      (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
      (bitWordValue (naturalCeilingWithWork (parentInitial query).1).1) query).1,
      ∀ t i, (draw (2 ^ eb) cell t i).2 ≤ S) :
    (preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).1 =
      (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi eb (fun b cell t i => (draw b cell t i).1) query).1 ∧
    (preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).2 ≤
      (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi eb (fun b cell t i => (draw b cell t i).1) query).2 * (S + 4) := by
  let b := 2 ^ eb
  let drawn (cell : ℕ × ℕ) : cellScaleReadDraw M b Q (nat F).value :=
    Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell)
  let cells := targetCellsWithWork (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1
    (bitWordValue (naturalCeilingWithWork (parentInitial query).1).1) query
  let read := fun cell => preparedComputedCellSourceWithWork source target parent P F exponent Q
    eM eF hM hF hP tau a parentInitial child initial current R hc hi b eb rfl (drawn cell) cell
  let plain := fun cell => preparedComputedCellReadWithWork source target parent P F exponent Q
    eM eF hM hF hP tau a parentInitial child initial current R hc hi b eb rfl
      (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F))
        (fun t i => (draw b cell t i).1)) cell
  have one (cell : ℕ × ℕ) (hcell : cell ∈ cells.1) :
      (read cell).1 = (plain cell).1 ∧ (read cell).2 ≤ (plain cell).2 * (S + 4) := by
    simpa only [read, plain, drawn] using
      computedCellSource_cast_cost source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb rfl (draw b cell) cell S (hs cell hcell)
  have h := filterMapWithWork_factor read plain cells.1 (S + 4) (by omega)
    (fun cell hcell => (one cell hcell).1) (fun cell hcell => (one cell hcell).2)
  have hcost :
      (parentInitial query).2 + (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).2 +
        (naturalCeilingWithWork (parentInitial query).1).2 + cells.2 +
        (filterMapWithWork read cells.1).2 + eb + 4 ≤
      ((parentInitial query).2 + (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).2 +
        (naturalCeilingWithWork (parentInitial query).1).2 + cells.2 +
        (filterMapWithWork plain cells.1).2 + eb + 4) * (S + 4) := by
    simpa only [Nat.add_assoc] using add_source_cost
      ((parentInitial query).2 + (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).2 +
        (naturalCeilingWithWork (parentInitial query).1).2 + cells.2)
      (eb + 4) (filterMapWithWork read cells.1).2 (filterMapWithWork plain cells.1).2 S h.2
  simpa only [preparedLocalGroupScaleSourceWithWork, preparedLocalGroupScaleReadWithWork,
    b, drawn, cells, read, plain] using And.intro h.1 hcost

theorem preparedLocalGroupScaleSourceWithWork_eq_cost (eb : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length)
    (S : ℕ) (hs : ∀ b cell t i, (draw b cell t i).2 ≤ S) :
    (preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).1 =
      (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi eb (fun b cell t i => (draw b cell t i).1) query).1 ∧
    (preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).2 ≤
      (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi eb (fun b cell t i => (draw b cell t i).1) query).2 * (S + 4) := by
  exact preparedLocalGroupScaleSourceWithWork_eq_cost_on source target parent P F exponent Q
    eM eF hM hF hP tau a parentInitial child initial current R hc hi eb draw query S
    (fun cell _ => hs (2 ^ eb) cell)

/-- Every admitted scale uses the source-aware whole-cell loop. -/
def preparedLocalCellGroupsSourceWithWork (N : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let count := max 1 N.bits.length
  let word := parentInitial query
  let groups := arithmeticFlatMapWithWork (fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a word.1
    if guard.1 then
      let selected := preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF
        hM hF hP tau a parentInitial child initial current R hc hi eb draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)) (List.range count)
  (groups.1, word.2 + groups.2 + count + N.bits.length + 2)

theorem preparedLocalCellGroupsSourceWithWork_eq_cost_on (N : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length)
    (S : ℕ)
    (hs : ∀ eb ∈ List.range (max 1 N.bits.length),
      (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1).1 = true →
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork (parentInitial query).1).1) query).1,
      ∀ t i, (draw (2 ^ eb) cell t i).2 ≤ S) :
    (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).1 =
      (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi N (fun b cell t i => (draw b cell t i).1) query).1 ∧
    (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).2 ≤
      (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi N (fun b cell t i => (draw b cell t i).1) query).2 * (S + 4) := by
  let read := fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1
    if guard.1 then
      let selected := preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF
        hM hF hP tau a parentInitial child initial current R hc hi eb draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)
  let plain := fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1
    if guard.1 then
      let selected := preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF
        hM hF hP tau a parentInitial child initial current R hc hi eb
        (fun b cell t i => (draw b cell t i).1) query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)
  have one (eb : ℕ) (heb : eb ∈ List.range (max 1 N.bits.length)) : (read eb).1 = (plain eb).1 ∧ (read eb).2 ≤ (plain eb).2 * (S + 4) := by
    dsimp only [read, plain]
    split_ifs with hguard
    · have h := preparedLocalGroupScaleSourceWithWork_eq_cost_on source target parent P F exponent Q
        eM eF hM hF hP tau a parentInitial child initial current R hc hi eb draw query S (hs eb heb hguard)
      have hcost := add_source_cost
        (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1).2 (eb + 4)
        (preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF
          hM hF hP tau a parentInitial child initial current R hc hi eb draw query).2
        (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF
          hM hF hP tau a parentInitial child initial current R hc hi eb
          (fun b cell t i => (draw b cell t i).1) query).2 S h.2
      simpa only [Nat.add_assoc] using And.intro h.1 hcost
    · have hvalue := Eq.refl ([] : List (BinaryBellmanAction (TargetInterval target.length)
        (Fin M × TargetInterval target.length) M))
      have hcost := Nat.le_mul_of_pos_right
        ((refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1).2 + eb + 4)
        (by omega : 0 < S + 4)
      simpa only using And.intro hvalue hcost
  have h := arithmeticFlatMapWithWork_factor read plain (List.range (max 1 N.bits.length))
    (S + 4) (by omega) (fun eb heb => (one eb heb).1) (fun eb heb => (one eb heb).2)
  have hcost :
      (parentInitial query).2 + (arithmeticFlatMapWithWork read (List.range (max 1 N.bits.length))).2 +
        max 1 N.bits.length + N.bits.length + 2 ≤
      ((parentInitial query).2 + (arithmeticFlatMapWithWork plain (List.range (max 1 N.bits.length))).2 +
        max 1 N.bits.length + N.bits.length + 2) * (S + 4) := by
    simpa only [Nat.add_assoc] using add_source_cost (parentInitial query).2
      (max 1 N.bits.length + N.bits.length + 2)
      (arithmeticFlatMapWithWork read (List.range (max 1 N.bits.length))).2
      (arithmeticFlatMapWithWork plain (List.range (max 1 N.bits.length))).2 S h.2
  simpa only [preparedLocalCellGroupsSourceWithWork, preparedLocalCellGroupsReadWithWork,
    read, plain] using And.intro h.1 hcost

theorem preparedLocalCellGroupsSourceWithWork_eq_cost (N : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length)
    (S : ℕ) (hs : ∀ b cell t i, (draw b cell t i).2 ≤ S) :
    (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).1 =
      (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi N (fun b cell t i => (draw b cell t i).1) query).1 ∧
    (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).2 ≤
      (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi N (fun b cell t i => (draw b cell t i).1) query).2 * (S + 4) := by
  exact preparedLocalCellGroupsSourceWithWork_eq_cost_on source target parent P F exponent Q
    eM eF hM hF hP tau a parentInitial child initial current R hc hi N draw query S
    (fun eb _ _ cell _ => hs (2 ^ eb) cell)

end Local
end BinaryFraction
end EditApproximation

end OAI
