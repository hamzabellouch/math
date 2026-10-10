import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalSourceKernel
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalReadValues

namespace OAI

/-! Exact local source-port values for arbitrary gathered answer lists.
No cost bound on unqueried coordinates enters these identities. -/

namespace EditApproximation

private theorem sourceDraw_project_cast (M b Q : ℕ) (f g : ℚ) (h : f = g)
    (draw : cellScaleReadDraw M b Q g) :
    (fun t i => ((Eq.mpr (congrArg (cellScaleReadDraw M b Q) h) draw) t i).1) =
      Eq.mpr (congrArg (BinaryFraction.cellScaleDraw M b Q) h) (fun t i => (draw t i).1) := by
  cases h
  rfl

namespace BinaryFraction
section Group
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

theorem preparedComputedCellSourceWithWork_value (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleReadDraw M b Q (nat F).value) (cell : ℕ × ℕ) :
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).1 =
      (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb hb (fun t i => (draw t i).1) cell).1 := by
  have h := preparedCellGroupSourceWithWork_value source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current R R hc hi
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell
  simpa only [preparedComputedCellSourceWithWork, preparedComputedCellReadWithWork] using h

private theorem computedCellSource_cast_value (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleReadDraw M b Q F) (cell : ℕ × ℕ) :
    (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb
      (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) draw) cell).1 =
    (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb
      (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (fun t i => (draw t i).1)) cell).1 := by
  have h := preparedComputedCellSourceWithWork_value source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial current R hc hi b eb hb
    (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) draw) cell
  rw [sourceDraw_project_cast M b Q _ _ (nat_value F) draw] at h
  exact h

theorem preparedLocalGroupScaleSourceWithWork_value (eb : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).1 =
      (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi eb (fun b cell t i => (draw b cell t i).1) query).1 := by
  simp only [preparedLocalGroupScaleSourceWithWork, preparedLocalGroupScaleReadWithWork,
    filterMapWithWork_value]
  apply List.filterMap_congr
  intro cell _
  have h := computedCellSource_cast_value source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial current R hc hi (2 ^ eb) eb rfl (draw (2 ^ eb) cell) cell
  simpa only using h

theorem preparedLocalCellGroupsSourceWithWork_value (N : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).1 =
      (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi N (fun b cell t i => (draw b cell t i).1) query).1 := by
  simp only [preparedLocalCellGroupsSourceWithWork, preparedLocalCellGroupsReadWithWork,
    arithmeticFlatMapWithWork_value]
  apply List.flatMap_congr
  intro eb _
  split_ifs
  · have h := preparedLocalGroupScaleSourceWithWork_value source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi eb draw query
    simpa only using h
  · rfl

theorem preparedLocalCellGroupsSourceWithWork_semantic_value (N : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).1 =
      (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP tau a
        (fun r => (parentInitial r).1) (fun i r => (child i r).1)
        (fun i r => (initial i r).1) (fun i r => (current i r).1)
        (fun b cell t i => (draw b cell t i).1) query).1 :=
  (preparedLocalCellGroupsSourceWithWork_value source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial current R hc hi N draw query).trans
  (preparedLocalCellGroupsReadWithWork_value_only source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial current R hc hi N (fun b cell t i => (draw b cell t i).1) query)
end Group

section Online
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)

theorem preparedLocalOnlineActionsSourceWithWork_semantic_value (N : ℕ)
    (query : TargetInterval target.length) :
    (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
      (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
        (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t (fun b q => (integer b q).1) query).1 :=
  (preparedLocalOnlineActionsSourceWithWork_value source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial table R hc hi t integer N query).trans
  (preparedLocalOnlineActionsReadWithWork_value_only source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial table R hc hi t (fun b q => (integer b q).1) N query)
end Online

end BinaryFraction
end EditApproximation

end OAI
