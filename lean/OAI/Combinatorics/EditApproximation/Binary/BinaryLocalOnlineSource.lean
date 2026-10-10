import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalOnlineReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryReadCostBounds

namespace OAI

/-! Online candidate selection charges the finite source-buffer decoder
at the point where its integer is consumed. Ineligible centers do not
read a random coordinate. -/

namespace EditApproximation.BinaryFraction
section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)

def preparedLocalOnlineScaleSourceWithWork (e : ℕ) (query : TargetInterval target.length) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let b := 2 ^ e
  let spacing := seedGridSpacingWithWork b P
  let center := roundStateWithWork (bitWordValue spacing.1) (seedGridSpacingWithWork_pos b P hP) query
  let word := parentInitial center.1
  let eligible := centerEligibilityWithWork b F a word.1
  if eligible.1 then
    let sample := integer b center.1
    let selected := preparedOnlineReadWithWork source target parent P F exponent H b (Nat.two_pow_pos e) hP
      tau eta kappa child initial table R hc hi t center.1 sample.1
    (selected.1, spacing.2 + center.2 + word.2 + eligible.2 + selected.2 + sample.2 + e + 5)
  else (none, spacing.2 + center.2 + word.2 + eligible.2 + e + 3)

theorem preparedLocalOnlineScaleSourceWithWork_value (e : ℕ) (query : TargetInterval target.length) :
    (preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).1 =
      (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) e query).1 := by
  unfold preparedLocalOnlineScaleSourceWithWork preparedLocalOnlineScaleReadWithWork
  dsimp only
  split_ifs <;> rfl

theorem preparedLocalOnlineScaleSourceWithWork_eq_cost_on (e : ℕ) (query : TargetInterval target.length)
    (S : ℕ)
    (hs : (centerEligibilityWithWork (2 ^ e) F a
      (parentInitial (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
        (seedGridSpacingWithWork_pos (2 ^ e) P hP) query).1).1).1 = true →
      (integer (2 ^ e) (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
        (seedGridSpacingWithWork_pos (2 ^ e) P hP) query).1).2 ≤ S) :
    (preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).1 =
      (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) e query).1 ∧
    (preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).2 ≤
      (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) e query).2 * (S + 4) := by
  unfold preparedLocalOnlineScaleSourceWithWork preparedLocalOnlineScaleReadWithWork
  dsimp only
  split_ifs with hguard
  · refine ⟨rfl, ?_⟩
    have hsample := hs hguard
    nlinarith only [hsample]
  · exact ⟨rfl, by nlinarith only [Nat.zero_le S]⟩
theorem preparedLocalOnlineScaleSourceWithWork_eq_cost (e : ℕ) (query : TargetInterval target.length)
    (S : ℕ) (hs : ∀ b q, (integer b q).2 ≤ S) :
    (preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).1 =
      (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) e query).1 ∧
    (preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).2 ≤
      (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) e query).2 * (S + 4) := by
  exact preparedLocalOnlineScaleSourceWithWork_eq_cost_on source target parent P F exponent H hP
    tau a eta kappa parentInitial child initial table R hc hi t integer e query S (fun _ => hs _ _)

def preparedLocalOnlineActionsSourceWithWork (N : ℕ) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let word := parentInitial query
  let scales := queryExponentsWithWork N F a word.1
  let selected := filterMapWithWork
    (fun e => preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query) scales.1
  (selected.1, word.2 + scales.2 + selected.2 + 1)

theorem preparedLocalOnlineActionsSourceWithWork_value (N : ℕ) (query : TargetInterval target.length) :
    (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
      (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) N query).1 := by
  simp only [preparedLocalOnlineActionsSourceWithWork, preparedLocalOnlineActionsReadWithWork,
    filterMapWithWork_value, preparedLocalOnlineScaleSourceWithWork_value]

theorem preparedLocalOnlineActionsSourceWithWork_eq_cost_on (N : ℕ) (query : TargetInterval target.length)
    (S : ℕ)
    (hs : ∀ e ∈ (queryExponentsWithWork N F a (parentInitial query).1).1,
      (centerEligibilityWithWork (2 ^ e) F a
        (parentInitial (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) query).1).1).1 = true →
        (integer (2 ^ e) (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) query).1).2 ≤ S) :
    (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
      (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) N query).1 ∧
    (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).2 ≤
      (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) N query).2 * (S + 4) := by
  have h := filterMapWithWork_factor
    (fun e => preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query)
    (fun e => preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t (fun b q => (integer b q).1) e query)
    (queryExponentsWithWork N F a (parentInitial query).1).1 (S + 4) (by omega)
    (fun e he => (preparedLocalOnlineScaleSourceWithWork_eq_cost_on source target parent P F exponent H hP
      tau a eta kappa parentInitial child initial table R hc hi t integer e query S (hs e he)).1)
    (fun e he => (preparedLocalOnlineScaleSourceWithWork_eq_cost_on source target parent P F exponent H hP
      tau a eta kappa parentInitial child initial table R hc hi t integer e query S (hs e he)).2)
  unfold preparedLocalOnlineActionsSourceWithWork preparedLocalOnlineActionsReadWithWork
  dsimp only
  rw [h.1]
  exact ⟨rfl, by nlinarith only [h.2]⟩
theorem preparedLocalOnlineActionsSourceWithWork_eq_cost (N : ℕ) (query : TargetInterval target.length)
    (S : ℕ) (hs : ∀ b q, (integer b q).2 ≤ S) :
    (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
      (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) N query).1 ∧
    (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).2 ≤
      (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) N query).2 * (S + 4) := by
  exact preparedLocalOnlineActionsSourceWithWork_eq_cost_on source target parent P F exponent H hP
    tau a eta kappa parentInitial child initial table R hc hi t integer N query S
    (fun e _ _ => hs _ _)

end Local
end EditApproximation.BinaryFraction

end OAI
