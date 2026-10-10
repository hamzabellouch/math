import OAI.Combinatorics.EditApproximation.Binary.BinaryCellReadCosts
import OAI.Combinatorics.EditApproximation.Binary.BinaryOnlineReadCosts
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGroupReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalOnlineReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeReads

namespace OAI

/-! The outer local loops preserve the same lookup factor, including
initial-value reads at the query and at rounded representative centers. -/

namespace EditApproximation
namespace BinaryFraction

theorem cost_replace_with_read (a c old new r R : ℕ) (hc : c ≤ a * tableReadFactor R)
    (hr : r ≤ R) (ha : a + 1 ≤ old) (hn : new + a ≤ old + c + r) :
    new ≤ old * tableReadFactor R := by
  have hK : R + 1 ≤ tableReadFactor R := by unfold tableReadFactor; omega
  have h := cost_factor_with_read a c (old - a) r R (tableReadFactor R)
    hc hr (by omega) hK
  have he : a + (old - a) = old := by omega
  rw [he] at h
  exact (by omega : new ≤ r + c + (old - a)).trans h

section Group
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

theorem preparedComputedCellReadWithWork_factor (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hcurrent : ∀ i q, (current i q).2 ≤ R) :
    (preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb hb draw cell).2 ≤
      (preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF hM hb hF hP
        tau a (fun r => (parentInitial r).1) (fun i q => (child i q).1)
        (fun i q => (initial i q).1) (fun i q => (current i q).1) draw cell).2 * tableReadFactor R := by
  have h := preparedCellGroupReadWithWork_factor source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
    R hc hi (groupScalesWithWork eM eb eF).1
    (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell hp hcurrent
  unfold preparedComputedCellReadWithWork preparedComputedCellGroupWithWork
  dsimp only
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem preparedLocalGroupScaleReadWithWork_factor (eb : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hcurrent : ∀ i q, (current i q).2 ≤ R) :
    (preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi eb draw query).2 ≤
      (preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb hM hF hP tau a
        (fun r => (parentInitial r).1) (fun i q => (child i q).1)
        (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query).2 * tableReadFactor R := by
  have hs := filterMapWithWork_factor
    (fun cell => preparedComputedCellReadWithWork source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi (2 ^ eb) eb rfl
      (Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell)) cell)
    (fun cell => preparedComputedCellGroupWithWork source target parent (2 ^ eb) P F exponent Q eM eb eF
      hM rfl hF hP tau a (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1)
      (Eq.mpr (congrArg (cellScaleDraw M (2 ^ eb) Q) (nat_value F)) (draw (2 ^ eb) cell)) cell)
    (targetCellsWithWork (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
      (bitWordValue (naturalCeilingWithWork (parentInitial query).1).1) query).1
    (tableReadFactor R) (tableReadFactor_pos R)
    (fun cell _ => preparedComputedCellReadWithWork_eq source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi _ eb rfl _ cell hp hcurrent)
    (fun cell _ => preparedComputedCellReadWithWork_factor source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi _ eb rfl _ cell hp hcurrent)
  unfold preparedLocalGroupScaleReadWithWork preparedLocalGroupScaleWithWork
  dsimp only
  apply cost_replace_with_read _ _ _ _ (parentInitial query).2 R hs.2 (hp query) <;> omega

theorem preparedLocalCellGroupsReadWithWork_factor (N : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (hcurrent : ∀ i q, (current i q).2 ≤ R) :
    (preparedLocalCellGroupsReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi N draw query).2 ≤
      (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP tau a
        (fun r => (parentInitial r).1) (fun i q => (child i q).1)
        (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query).2 * tableReadFactor R := by
  let first := fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1
    if guard.1 then
      let selected := preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF
        hM hF hP tau a parentInitial child initial current R hc hi eb draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)
  let second := fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1
    if guard.1 then
      let selected := preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
        hM hF hP tau a (fun r => (parentInitial r).1) (fun i q => (child i q).1)
        (fun i q => (initial i q).1) (fun i q => (current i q).1) draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)
  have h := arithmeticFlatMapWithWork_factor first second (List.range (max 1 N.bits.length))
    (tableReadFactor R) (tableReadFactor_pos R) (by
      intro eb _
      dsimp only [first, second]
      split_ifs
      · have heq := preparedLocalGroupScaleReadWithWork_eq source target parent P F exponent Q eM eF
          hM hF hP tau a parentInitial child initial current R hc hi eb draw query hp hcurrent
        simpa only using heq
      · rfl) (by
      intro eb _
      dsimp only [first, second]
      split_ifs
      · have hs := preparedLocalGroupScaleReadWithWork_factor source target parent P F exponent Q eM eF
          hM hF hP tau a parentInitial child initial current R hc hi eb draw query hp hcurrent
        apply cost_replace_factor _ _ _ _ _ hs (tableReadFactor_pos R) <;> omega
      · exact Nat.le_mul_of_pos_right _ (by have := tableReadFactor_pos R; omega))
  change (parentInitial query).2 + (arithmeticFlatMapWithWork first _).2 + _ + _ + 2 ≤
    ((arithmeticFlatMapWithWork second _).2 + _ + _ + 2) * tableReadFactor R
  apply cost_replace_with_read _ _ _ _ (parentInitial query).2 R h.2 (hp query) <;> omega

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

theorem preparedLocalOnlineScaleReadWithWork_factor (e : ℕ) (query : TargetInterval target.length)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).2 ≤
      (preparedLocalOnlineScaleWithWork source target parent P F exponent H e hP tau a eta kappa
        (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t integer query).2 * tableReadFactor R := by
  let center := (roundStateWithWork
    (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
    (seedGridSpacingWithWork_pos (2 ^ e) P hP) query).1
  have hpcenter := hp center
  dsimp only [center] at hpcenter
  unfold preparedLocalOnlineScaleReadWithWork preparedLocalOnlineScaleWithWork
  dsimp only
  split_ifs
  · have h := preparedOnlineReadWithWork_factor source target parent P F exponent H (2 ^ e)
      (Nat.two_pow_pos e) hP tau eta kappa child initial table R hc hi t
      center (integer (2 ^ e) center) ht
    dsimp only [center] at h
    apply cost_replace_with_read _ _ _ _ _ R h hpcenter <;> omega
  · apply cost_replace_with_read 0 0 _ _ _ R (by simp) hpcenter <;> omega

theorem preparedLocalOnlineActionsReadWithWork_factor (N : ℕ) (query : TargetInterval target.length)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).2 ≤
      (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
        (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t integer query).2 * tableReadFactor R := by
  have hs := filterMapWithWork_factor
    (fun e => preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query)
    (fun e => preparedLocalOnlineScaleWithWork source target parent P F exponent H e hP tau a eta kappa
      (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t integer query)
    (queryExponentsWithWork N F a (parentInitial query).1).1
    (tableReadFactor R) (tableReadFactor_pos R)
    (fun e _ => preparedLocalOnlineScaleReadWithWork_eq source target parent P F exponent H hP
      tau a eta kappa parentInitial child initial table R hc hi t integer e query ht)
    (fun e _ => preparedLocalOnlineScaleReadWithWork_factor source target parent P F exponent H hP
      tau a eta kappa parentInitial child initial table R hc hi t integer e query hp ht)
  unfold preparedLocalOnlineActionsReadWithWork preparedLocalOnlineActionsWithWork
  dsimp only
  apply cost_replace_with_read _ _ _ _ (parentInitial query).2 R hs.2 (hp query) <;> omega

end Online
end BinaryFraction
end EditApproximation

end OAI
