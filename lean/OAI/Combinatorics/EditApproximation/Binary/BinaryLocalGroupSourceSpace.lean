import OAI.Combinatorics.EditApproximation.Binary.BinaryCellSourceSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGroupSource
import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSetupSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



private theorem transportedSourceAllocation_le {M b Q : ℕ} {f g : ℚ} (h : f = g)
    (draw : cellScaleReadDraw M b Q g)
    (allocation : ∀ t : Fin (groupDyadicScales M b g).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b g t)) → ℕ)
    (ha : ∀ t i, allocation t i ≤ (draw t i).2) :
    ∀ t i, (Eq.mpr (congrArg (fun f => ∀ t : Fin (groupDyadicScales M b f).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b f t)) → ℕ) h) allocation) t i ≤
      (Eq.mpr (congrArg (cellScaleReadDraw M b Q) h) draw t i).2 := by
  cases h
  exact ha

namespace BinaryFraction
section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (parentAllocation : TargetInterval target.length → ℕ)
  (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)

def preparedComputedCellSourceAllocation (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleReadDraw M b Q (nat F).value)
    (drawAllocation : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → ℕ)
    (cell : ℕ × ℕ) : ℕ :=
  groupScalesAllocation eM eb eF +
    preparedCellGroupSourceAllocation source target parent b P F exponent Q
      (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
      R R hc hi (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF)
      draw parentAllocation childAllocation initialAllocation currentAllocation drawAllocation cell

theorem preparedComputedCellSourceAllocation_le_work (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleReadDraw M b Q (nat F).value)
    (drawAllocation : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → ℕ)
    (cell : ℕ × ℕ)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hcur : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (hd : ∀ t i, drawAllocation t i ≤ (draw t i).2) :
    preparedComputedCellSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      b eb hb draw drawAllocation cell ≤
      (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb hb draw cell).2 := by
  have hs := groupScalesAllocation_le_work eM eb eF
  have ha := preparedCellGroupSourceAllocation_le_work source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current R R hc hi
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF)
    draw parentAllocation childAllocation initialAllocation currentAllocation drawAllocation cell hp hca hia hcur hd
  unfold preparedComputedCellSourceAllocation preparedComputedCellSourceWithWork
  dsimp only
  omega

variable (draw : CellGroupReadDraws M F Q) (drawAllocation : CellGroupSourceAllocations M F Q)

private def castGroupSourceAllocation (b : ℕ) (cell : ℕ × ℕ) :
    ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → ℕ :=
  Eq.mpr (congrArg (fun f => ∀ t : Fin (groupDyadicScales M b f).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b f t)) → ℕ) (nat_value F)) (drawAllocation b cell)

private theorem castGroupSourceAllocation_le (b : ℕ) (cell : ℕ × ℕ)
    (hd : ∀ t i, drawAllocation b cell t i ≤ (draw b cell t i).2) :
    ∀ t i, castGroupSourceAllocation F Q drawAllocation b cell t i ≤
      (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell) t i).2 := by
  exact transportedSourceAllocation_le (nat_value F) (draw b cell) (drawAllocation b cell) hd

def preparedLocalGroupScaleSourceAllocation (eb : ℕ) (query : TargetInterval target.length) : ℕ :=
  let b := 2 ^ eb
  let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1
  let radius := (naturalCeilingWithWork (parentInitial query).1).1
  let cells := (targetCellsWithWork side (bitWordValue radius) query).1
  parentAllocation query + canonicalMulAllocation (inversePowerTwo exponent) (nat b) +
    naturalCeilingAllocation (parentInitial query).1 + targetCellsAllocation side (bitWordValue radius) query +
    filterMapAllocation (fun cell =>
      preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb rfl
        (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell)) cell)
      (fun cell => preparedComputedCellSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
        b eb rfl (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell))
        (castGroupSourceAllocation F Q drawAllocation b cell) cell) cells + eb

theorem preparedLocalGroupScaleSourceAllocation_le_work (eb : ℕ) (query : TargetInterval target.length)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hcur : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (hd : ∀ b cell t i, drawAllocation b cell t i ≤ (draw b cell t i).2) :
    preparedLocalGroupScaleSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      draw drawAllocation eb query ≤
      (preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi eb draw query).2 := by
  let b := 2 ^ eb
  let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1
  let cells := (targetCellsWithWork side (bitWordValue (naturalCeilingWithWork (parentInitial query).1).1) query).1
  have hm := canonicalMulAllocation_le_work (inversePowerTwo exponent) (nat b)
  have hr := naturalCeilingAllocation_le_work (parentInitial query).1
  have ht := targetCellsAllocation_le_work side (bitWordValue (naturalCeilingWithWork (parentInitial query).1).1) query
  have hf := filterMapAllocation_le_work
    (fun cell => preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb rfl
      (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell)) cell)
    (fun cell => preparedComputedCellSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      b eb rfl (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell))
      (castGroupSourceAllocation F Q drawAllocation b cell) cell) cells
    (fun cell _ => preparedComputedCellSourceAllocation_le_work source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      b eb rfl _ _ cell hp hca hia hcur (castGroupSourceAllocation_le F Q draw drawAllocation b cell (hd b cell)))
  have hq := hp query
  unfold preparedLocalGroupScaleSourceAllocation preparedLocalGroupScaleSourceWithWork
  dsimp only [b, side, cells] at hm ht hf ⊢
  omega

def localGroupSourceScaleBlock (eb : ℕ) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) × ℕ :=
  let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1
  if guard.1 then
    let selected := preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi eb draw query
    (selected.1, guard.2 + selected.2 + eb + 4)
  else ([], guard.2 + eb + 4)

def localGroupSourceScaleBlockAllocation (eb : ℕ) (query : TargetInterval target.length) : ℕ :=
  refinementScaleGuardAllocation F (2 ^ eb) a (parentInitial query).1 + eb +
    if (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1).1 then
      preparedLocalGroupScaleSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
        draw drawAllocation eb query
    else 0

theorem localGroupSourceScaleBlockAllocation_le_work (eb : ℕ) (query : TargetInterval target.length)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hcur : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (hd : ∀ b cell t i, drawAllocation b cell t i ≤ (draw b cell t i).2) :
    localGroupSourceScaleBlockAllocation source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      draw drawAllocation eb query ≤
      (localGroupSourceScaleBlock source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi draw eb query).2 := by
  have costBound (g g' s s' e : ℕ) (hg : g ≤ g') (hs : s ≤ s') :
      g + e + s ≤ g' + s' + e + 4 := by
    omega
  have hg := refinementScaleGuardAllocation_le_work F (2 ^ eb) a (parentInitial query).1
  have hs := preparedLocalGroupScaleSourceAllocation_le_work source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
    draw drawAllocation eb query hp hca hia hcur hd
  unfold localGroupSourceScaleBlockAllocation localGroupSourceScaleBlock
  dsimp only
  split_ifs <;> dsimp only
  · exact costBound _ _ _ _ _ hg hs
  · exact (Nat.add_le_add_right hg eb).trans (Nat.le_add_right _ 4)

def preparedLocalCellGroupsSourceAllocation (N : ℕ) (query : TargetInterval target.length) : ℕ :=
  let count := max 1 N.bits.length
  parentAllocation query + count + N.bits.length +
    arithmeticFlatMapAllocation
      (fun eb => localGroupSourceScaleBlock source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi draw eb query)
      (fun eb => localGroupSourceScaleBlockAllocation source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
        draw drawAllocation eb query) (List.range count)

theorem preparedLocalCellGroupsSourceAllocation_le_work (N : ℕ) (query : TargetInterval target.length)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hcur : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (hd : ∀ b cell t i, drawAllocation b cell t i ≤ (draw b cell t i).2) :
    preparedLocalCellGroupsSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      draw drawAllocation N query ≤
      (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi N draw query).2 := by
  have hm := arithmeticFlatMapAllocation_le_work
    (fun eb => localGroupSourceScaleBlock source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi draw eb query)
    (fun eb => localGroupSourceScaleBlockAllocation source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      draw drawAllocation eb query) (List.range (max 1 N.bits.length))
    (fun eb _ => localGroupSourceScaleBlockAllocation_le_work source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      draw drawAllocation eb query hp hca hia hcur hd)
  have hq := hp query
  change _ ≤ (parentInitial query).2 +
    (arithmeticFlatMapWithWork (fun eb => localGroupSourceScaleBlock source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi draw eb query) (List.range (max 1 N.bits.length))).2 +
    max 1 N.bits.length + N.bits.length + 2
  unfold preparedLocalCellGroupsSourceAllocation
  dsimp only
  omega

end Local
end BinaryFraction
end EditApproximation

end OAI
