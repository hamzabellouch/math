import OAI.Combinatorics.EditApproximation.Binary.BinaryOnlineSourceSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryEligibilitySpace

namespace OAI

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
  (parentAllocation : TargetInterval target.length → ℕ)
  (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
  (tableAllocation : ℕ → Fin M × TargetInterval target.length → ℕ)
  (integerAllocation : ℕ → TargetInterval target.length → ℕ)

def preparedLocalOnlineScaleSourceAllocation (e : ℕ) (query : TargetInterval target.length) : ℕ :=
  let b := 2 ^ e
  let center := (roundStateWithWork (bitWordValue (seedGridSpacingWithWork b P).1)
    (seedGridSpacingWithWork_pos b P hP) query).1
  seedGridSpacingAllocation b P + roundStateAllocation (bitWordValue (seedGridSpacingWithWork b P).1) query +
    parentAllocation center + centerEligibilityAllocation b F a (parentInitial center).1 + e +
    if (centerEligibilityWithWork b F a (parentInitial center).1).1 then
      integerAllocation b center + preparedOnlineReadAllocation source target parent P F exponent H b
        (Nat.two_pow_pos e) hP tau eta kappa child initial table R hc hi
        childAllocation initialAllocation tableAllocation t center (integer b center).1
    else 0

theorem preparedLocalOnlineScaleSourceAllocation_le_work (e : ℕ) (query : TargetInterval target.length)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hta : ∀ s q, tableAllocation s q ≤ (table s q).2)
    (hint : ∀ b q, integerAllocation b q ≤ (integer b q).2) :
    preparedLocalOnlineScaleSourceAllocation source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer parentAllocation childAllocation initialAllocation
      tableAllocation integerAllocation e query ≤
      3 * (preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t integer e query).2 := by
  have costBound (s s' r r' p p' g g' i i' a a' e k : ℕ)
      (hs : s ≤ s') (hr : r ≤ r') (hp : p ≤ p') (hg : g ≤ g')
      (hi : i ≤ i') (ha : a ≤ 3 * a') :
      s + r + p + g + e + (i + a) ≤ 3 * (s' + r' + p' + g' + a' + i' + e + k) := by
    omega
  have emptyBound (s s' r r' p p' g g' e : ℕ)
      (hs : s ≤ s') (hr : r ≤ r') (hp : p ≤ p') (hg : g ≤ g') :
      s + r + p + g + e + 0 ≤ 3 * (s' + r' + p' + g' + e + 3) := by
    omega
  let b := 2 ^ e
  let center := (roundStateWithWork (bitWordValue (seedGridSpacingWithWork b P).1)
    (seedGridSpacingWithWork_pos b P hP) query).1
  have hs := seedGridSpacingAllocation_le_work b P
  have hr := roundStateAllocation_le_work (bitWordValue (seedGridSpacingWithWork b P).1)
    (seedGridSpacingWithWork_pos b P hP) query
  have hg := centerEligibilityAllocation_le_work b F a (parentInitial center).1
  have hp' := hp center
  have hint' := hint b center
  have hsample := preparedOnlineReadAllocation_le_work source target parent P F exponent H b
    (Nat.two_pow_pos e) hP tau eta kappa child initial table R hc hi
    childAllocation initialAllocation tableAllocation t center (integer b center).1 hca hia hta
  unfold preparedLocalOnlineScaleSourceAllocation preparedLocalOnlineScaleSourceWithWork
  dsimp only
  split_ifs <;> dsimp only [b, center] at hs hr hg hp' hint' hsample ⊢
  · exact costBound _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs hr hp' hg hint' hsample
  · exact emptyBound _ _ _ _ _ _ _ _ _ hs hr hp' hg

def preparedLocalOnlineActionsSourceAllocation (N : ℕ) (query : TargetInterval target.length) : ℕ :=
  parentAllocation query + queryExponentsAllocation N F a (parentInitial query).1 +
    filterMapAllocation
      (fun e => preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t integer e query)
      (fun e => preparedLocalOnlineScaleSourceAllocation source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t integer parentAllocation childAllocation initialAllocation
        tableAllocation integerAllocation e query)
      (queryExponentsWithWork N F a (parentInitial query).1).1

theorem preparedLocalOnlineActionsSourceAllocation_le_work (N : ℕ) (query : TargetInterval target.length)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hta : ∀ s q, tableAllocation s q ≤ (table s q).2)
    (hint : ∀ b q, integerAllocation b q ≤ (integer b q).2) :
    preparedLocalOnlineActionsSourceAllocation source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer parentAllocation childAllocation initialAllocation
      tableAllocation integerAllocation N query ≤
      3 * (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t integer N query).2 := by
  have hq := hp query
  have he := queryExponentsAllocation_le_work N F a (parentInitial query).1
  have hm := filterMapAllocation_le_three_work
    (fun e => preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query)
    (fun e => preparedLocalOnlineScaleSourceAllocation source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer parentAllocation childAllocation initialAllocation
      tableAllocation integerAllocation e query)
    (queryExponentsWithWork N F a (parentInitial query).1).1
    (fun e _ => preparedLocalOnlineScaleSourceAllocation_le_work source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer parentAllocation childAllocation initialAllocation
      tableAllocation integerAllocation e query hp hca hia hta hint)
  unfold preparedLocalOnlineActionsSourceAllocation preparedLocalOnlineActionsSourceWithWork
  dsimp only
  omega

end Local
end EditApproximation.BinaryFraction

end OAI
