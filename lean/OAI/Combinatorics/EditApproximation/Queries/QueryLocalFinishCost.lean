import OAI.Combinatorics.EditApproximation.Queries.QueryFinishCost
import OAI.Combinatorics.EditApproximation.Queries.QuerySelectorGeometry
import OAI.Combinatorics.EditApproximation.Queries.QueryActionInputCost

namespace OAI

/-! The executed refinement tail, with its actual selected actions and
its final deduplicated current-input buffer. -/

namespace EditApproximation.BinaryFraction

def queryFinishReadBudget (M B Rp earlierCount groups online : ℕ) : ℕ :=
  Rp + 2 + earlierCount * (32 * B + 12) + (groups + online) * M * (24 * B + 9)

section Finish
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (draw : CountedCellGroupDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (earlierKeys : List (Fin M × ℕ × TargetInterval target.length)) (earlierWords : List BinaryFraction)
  (sharedKeys : List (Fin M × TargetInterval target.length)) (sharedWords currentWords : List BinaryFraction)
  (q : TargetInterval target.length)

theorem queryLocalRefinement_finish_bounds (B Rp earlierCount : ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (ht : Nat.size t ≤ B) (ha : a.width ≤ B) (hd : delta.width ≤ B)
    (hpw : ∀ r, (parentInitial r).1.width ≤ B) (hpr : ∀ r, (parentInitial r).2 ≤ Rp)
    (hpn : 0 ≤ (parentInitial q).1.value)
    (hew : ∀ w ∈ earlierWords, w.width ≤ B) (hcw : ∀ w ∈ currentWords, w.width ≤ B)
    (het : ∀ key ∈ earlierKeys, Nat.size key.2.1 ≤ B) (hel : earlierKeys.length ≤ earlierCount) :
    let groups := (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
      tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q).1
    let online := (queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R hc hi t integer earlierKeys earlierWords q).1
    let keys := (queryNeededInputsWithWork groups online).1
    let G := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
    let lookup := queryFinishReadBudget M B Rp earlierCount G (B + 1)
    (queryRefinementFinishWithWork parent N P F a delta parentInitial t earlierKeys earlierWords
      groups online keys currentWords q).1.width ≤ preparedKernelWordBudget M B ∧
    (queryRefinementFinishWithWork parent N P F a delta parentInitial t earlierKeys earlierWords
      groups online keys currentWords q).2 ≤ queryRefinementFinishBitBudget M P F B lookup G (B + 1) := by
  let groups := (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
    tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q).1
  let online := (queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
    parentInitial child initial R hc hi t integer earlierKeys earlierWords q).1
  let keys := (queryNeededInputsWithWork groups online).1
  let G := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let lookup := queryFinishReadBudget M B Rp earlierCount G (B + 1)
  have hg := queryGroupSelectWithWork_geometry source target parent N P F exponent Q eM eF hP hM hF
    tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q B hN hny hpn
  have hgc := (queryGroupSelectWithWork_geometry source target parent N P F exponent Q eM eF hP hM hF
    tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q (B + 4)
    (by omega) (by omega) hpn).2
  have ho := queryOnlineSelectWithWork_geometry source target parent N P F exponent H hP tau a eta kappa
    parentInitial child initial R hc hi t integer earlierKeys earlierWords q B hN
  have hk := (queryNeededInputsWithWork_bounds groups online B hMb (by omega)).1
  have hkl : keys.length ≤ (G + (B + 1)) * M := by
    exact hk.trans (Nat.mul_le_mul_right M (Nat.add_le_add hg.1 ho.1))
  apply queryRefinementFinishWithWork_bounds parent N P F B lookup G (B + 1) a delta parentInitial t
    earlierKeys earlierWords groups online keys currentWords q hB hP
    (by rw [hF]; exact Nat.one_le_two_pow) hN hnx hny hMb hPb hFb ha hd hpw
  · intro r
    have hr := hpr r
    dsimp only [lookup, queryFinishReadBudget]
    omega
  · intro input
    exact queryHistoryReadWithWork_width earlierKeys earlierWords (t - 1) input B (by omega) hew
  · intro input
    have hr := queryHistoryReadWithWork_cost earlierKeys earlierWords (t - 1) input B hMb (by omega)
      ((Nat.size_le_size (Nat.sub_le t 1)).trans ht) het
    have hm := Nat.mul_le_mul_right (32 * B + 12) hel
    dsimp only [lookup, queryFinishReadBudget]
    omega
  · intro i r
    exact gatheredWordLookupWithWork_width _ keys currentWords (i, r) B (by omega) hcw
  · intro i r
    have hr := queryChildReadWithWork_cost keys currentWords i r B hMb (by omega)
    have hm := Nat.mul_le_mul_right (24 * B + 9) hkl
    dsimp only [lookup, queryFinishReadBudget]
    omega
  · exact hgc
  · intro action haction
    rw [ho.2 action haction]
    change 1 ≤ connectionWordBudget M (B + 4)
    unfold connectionWordBudget bandMassTotalStorageBudget
    omega
  · exact hg.1
  · exact ho.1

end Finish
end EditApproximation.BinaryFraction

end OAI
