import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGroupReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalOnlineReads
import OAI.Combinatorics.EditApproximation.Geometry.StateDomain

namespace OAI

/-! Value preservation of local data readers does not require a chosen
work cap for arbitrary answer tables. Finite bounds used below exist only
inside these proofs and are never constructed by the algorithm. -/

namespace EditApproximation.BinaryFraction

private theorem finite_work_bound {ι : Type*} [Fintype ι] (work : ι → ℕ) :
    ∃ R, ∀ i, work i ≤ R := by
  classical
  exact ⟨∑ i, work i, fun i => Finset.single_le_sum (f := work) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)⟩

section Group
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

theorem preparedComputedCellReadWithWork_value_only (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ) :
    (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).1 =
    (preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF hM hb hF hP
      tau a (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) draw cell).1 := by
  classical
  obtain ⟨Rp, hp⟩ := finite_work_bound (fun r => (parentInitial r).2)
  obtain ⟨Rc, hcur⟩ := finite_work_bound (fun iq : Fin M × TargetInterval target.length =>
    (current iq.1 iq.2).2)
  have h := preparedCellGroupReadWithWork_eq source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
    R R hc hi (groupScalesWithWork eM eb eF).1
    (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell Rp Rc hp
    (fun i q => hcur (i, q))
  simpa only [preparedComputedCellReadWithWork, preparedComputedCellGroupWithWork] using h

theorem preparedLocalGroupScaleReadWithWork_value_only (eb : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).1 =
    (preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb hM hF hP tau a
      (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query).1 := by
  simp only [preparedLocalGroupScaleReadWithWork, preparedLocalGroupScaleWithWork,
    filterMapWithWork_value]
  apply List.filterMap_congr
  intro cell _
  have h := preparedComputedCellReadWithWork_value_only source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial current R hc hi (2 ^ eb) eb rfl
    (Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell)) cell
  simpa only using h

theorem preparedLocalCellGroupsReadWithWork_value_only (N : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
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
  · have h := preparedLocalGroupScaleReadWithWork_value_only source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi eb draw query
    simpa only using h
  · rfl
end Group

section Online
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ)

private theorem preparedOnlineReadWithWork_cap_irrel (b : ℕ) (hb : 0 < b)
    (R' : ℕ) (hc' : ∀ i q, (child i q).2 ≤ R') (hi' : ∀ i q, (initial i q).2 ≤ R')
    (center : TargetInterval target.length) (sample : ℕ) :
    preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center sample =
    preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R' hc' hi' t center sample := by
  rfl

theorem preparedOnlineReadWithWork_value_only (b : ℕ) (hb : 0 < b)
    (center : TargetInterval target.length) (sample : ℕ) :
    (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center sample).1 =
    (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa
      (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t center sample).1 := by
  classical
  obtain ⟨S, hs⟩ := finite_work_bound (fun si : Fin (t + 2) × (Fin M × TargetInterval target.length) =>
    (table si.1.val si.2).2)
  let R' := max R S
  have hc' : ∀ i q, (child i q).2 ≤ R' := fun i q => (hc i q).trans (Nat.le_max_left _ _)
  have hi' : ∀ i q, (initial i q).2 ≤ R' := fun i q => (hi i q).trans (Nat.le_max_left _ _)
  rw [preparedOnlineReadWithWork_cap_irrel source target parent P F exponent H hP
    tau eta kappa child initial table R hc hi t b hb R' hc' hi' center sample]
  exact (preparedOnlineReadWithWork_eq_cost source target parent P F exponent H b hb hP
    tau eta kappa child initial table R' hc' hi' t center sample (fun s hst iq =>
      (hs (⟨s, by omega⟩, iq)).trans (Nat.le_max_right R S))).1

theorem preparedLocalOnlineScaleReadWithWork_value_only (e : ℕ) (query : TargetInterval target.length) :
    (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).1 =
    (preparedLocalOnlineScaleWithWork source target parent P F exponent H e hP tau a eta kappa
      (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t integer query).1 := by
  unfold preparedLocalOnlineScaleReadWithWork preparedLocalOnlineScaleWithWork
  dsimp only
  split_ifs
  · exact preparedOnlineReadWithWork_value_only source target parent P F exponent H hP
      tau eta kappa child initial table R hc hi t (2 ^ e) (Nat.two_pow_pos e) _ _
  · rfl

theorem preparedLocalOnlineActionsReadWithWork_value_only (N : ℕ) (query : TargetInterval target.length) :
    (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
    (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
      (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t integer query).1 := by
  simp only [preparedLocalOnlineActionsReadWithWork, preparedLocalOnlineActionsWithWork,
    filterMapWithWork_value]
  apply List.filterMap_congr
  intro e _
  exact preparedLocalOnlineScaleReadWithWork_value_only source target parent P F exponent H hP
    tau a eta kappa parentInitial child initial table R hc hi t integer e query
end Online
end EditApproximation.BinaryFraction

end OAI
