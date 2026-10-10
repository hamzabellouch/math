import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryInputCost
import OAI.Combinatorics.EditApproximation.Queries.QueryDataBuffers

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryEarlierInputsWithWork_time {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent history : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (input : Fin M × ℕ × TargetInterval ny)
    (hi : input ∈ (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).1) :
    input.2.1 < history := by
  simp only [queryEarlierInputsWithWork, queryOrderedHistoryInputsWithWork_value] at hi
  have hm := (mem_orderedInputs historyInputCode (historyInputCode_injective M ny) _ input).mp hi
  rw [List.mem_toFinset] at hm
  exact queryRawHistoryInputsWithWork_time M parent P history hP _ input hm

def queryEarlierBufferReadBudget (M P F exponent history B : ℕ) : ℕ :=
  1 + queryHistoryInputsLength M P history (queryEarlierRepresentativesLength P F exponent B) * (32 * B + 12)

theorem queryEarlierInputsWithWork_readCost {nx ny : ℕ} (M N P F exponent history B Rp : ℕ)
    (parent : TargetInterval nx) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (words : List BinaryFraction)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (ht : Nat.size history ≤ B) (he : exponent + 1 ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, (initial r).1.width ≤ B) (hR : ∀ r, (initial r).2 ≤ Rp)
    (hw : 0 ≤ (initial q).1.value) (hPd : ∃ e : ℕ, P = 2 ^ e) :
    ∀ s ≤ history, ∀ input,
      (queryHistoryReadWithWork
        (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).1 words s input).2 ≤
        queryEarlierBufferReadBudget M P F exponent history B := by
  intro s hs input
  have hlen := (queryEarlierInputsWithWork_bounds M N P F exponent history B Rp parent hP a initial q
    hB hN hF hFpos hPb hnx hny hM ht he ha hi hR hw hPd).1
  have hread := queryHistoryReadWithWork_cost
    (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).1 words s input B hM hny
    ((Nat.size_le_size hs).trans ht) (fun key hk =>
      (Nat.size_le_size (queryEarlierInputsWithWork_time M parent N P F exponent history hP a initial q key hk).le).trans ht)
  exact hread.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) 1)

end EditApproximation.BinaryFraction

end OAI
