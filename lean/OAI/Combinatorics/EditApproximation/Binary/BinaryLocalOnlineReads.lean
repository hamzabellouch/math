import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedOnlineReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedLocalOnline

namespace OAI

/-! Query-local online scales explicitly read the initial value at the
query and at each rounded center before running the full band kernel. -/

namespace EditApproximation
namespace BinaryFraction

section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ)

def preparedLocalOnlineScaleReadWithWork (e : ℕ) (query : TargetInterval target.length) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let b := 2 ^ e
  let spacing := seedGridSpacingWithWork b P
  let center := roundStateWithWork (bitWordValue spacing.1) (seedGridSpacingWithWork_pos b P hP) query
  let word := parentInitial center.1
  let eligible := centerEligibilityWithWork b F a word.1
  if eligible.1 then
    let selected := preparedOnlineReadWithWork source target parent P F exponent H b (Nat.two_pow_pos e) hP
      tau eta kappa child initial table R hc hi t center.1 (integer b center.1)
    (selected.1, spacing.2 + center.2 + word.2 + eligible.2 + selected.2 + e + 4)
  else (none, spacing.2 + center.2 + word.2 + eligible.2 + e + 3)

theorem preparedLocalOnlineScaleReadWithWork_eq (e : ℕ) (query : TargetInterval target.length)
    (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).1 =
    (preparedLocalOnlineScaleWithWork source target parent P F exponent H e hP tau a eta kappa
      (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t integer query).1 := by
  unfold preparedLocalOnlineScaleReadWithWork preparedLocalOnlineScaleWithWork
  dsimp only
  split_ifs
  · exact (preparedOnlineReadWithWork_eq_cost source target parent P F exponent H (2 ^ e)
      (Nat.two_pow_pos e) hP tau eta kappa child initial table R hc hi t _ _ ht).1
  · rfl

def preparedLocalOnlineActionsReadWithWork (N : ℕ) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let word := parentInitial query
  let scales := queryExponentsWithWork N F a word.1
  let selected := filterMapWithWork
    (fun e => preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query) scales.1
  (selected.1, word.2 + scales.2 + selected.2 + 1)

theorem preparedLocalOnlineActionsReadWithWork_eq (N : ℕ) (query : TargetInterval target.length)
    (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
    (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
      (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t integer query).1 := by
  simp only [preparedLocalOnlineActionsReadWithWork, preparedLocalOnlineActionsWithWork,
    filterMapWithWork_value]
  apply List.filterMap_congr
  intro e _
  exact preparedLocalOnlineScaleReadWithWork_eq source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial table R hc hi t integer e query ht

end Local
end BinaryFraction
end EditApproximation

end OAI
