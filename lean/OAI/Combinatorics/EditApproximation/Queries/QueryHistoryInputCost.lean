import OAI.Combinatorics.EditApproximation.Queries.QueryBandInputCost
import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryCodeBounds

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryRawHistoryInputsWithWork_time {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (P history : ℕ) (hP : 0 < P) (representatives : List (ℕ × TargetInterval ny))
    (input : Fin M × ℕ × TargetInterval ny)
    (hi : input ∈ (queryRawHistoryInputsWithWork M parent P history representatives).1) :
    input.2.1 < history := by
  rw [queryRawHistoryInputsWithWork_value M parent P history hP] at hi
  obtain ⟨br, _, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hi
  exact List.mem_range.mp ht

def queryHistoryInputsLength (M P history count : ℕ) : ℕ :=
  count * (M * (history * (40 * P + 2) ^ 2))

def queryRawHistoryInputsBitBudget (M P history count B : ℕ) : ℕ :=
  let G := (40 * P + 2) ^ 2
  let C := wideChildGridBitBudget P (B + 1)
  count * (M * (C + history * (5 * G + 3) + history + 2 + history * G + 3) +
    M * (history * G) + 3) + M + 1

theorem queryRawHistoryInputsWithWork_dyadic_bounds {nx ny : ℕ}
    (M N P history count B : ℕ) (parent : TargetInterval nx) (hP : 0 < P)
    (representatives : List (ℕ × TargetInterval ny)) (hl : representatives.length ≤ count)
    (hs : ∀ br ∈ representatives, br.1 ∈ dyadicScales N)
    (hN : Nat.size N ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hPb : Nat.size P ≤ B) :
    (queryRawHistoryInputsWithWork M parent P history representatives).1.length ≤
      queryHistoryInputsLength M P history count ∧
    (queryRawHistoryInputsWithWork M parent P history representatives).2 ≤
      queryRawHistoryInputsBitBudget M P history count B := by
  have hb := queryRawHistoryInputsWithWork_bounds M parent P history representatives
    ((40 * P + 2) ^ 2) (wideChildGridBitBudget P (B + 1))
    (fun br _ i => by rw [wideChildGridWithWork_value _ _ _ _ _ hP]; exact wideChildStateList_length_le parent br.2 hP i)
    (fun br hbr i => wideChildGridWithWork_cost parent br.2 br.1 P (B + 1) i hP
      (by omega) (by omega) (by omega)
      ((dyadicScales_size_bound N br.1 (hs br hbr)).trans (by omega)) (by omega))
  constructor
  · exact hb.1.trans (Nat.mul_le_mul_right _ hl)
  · apply hb.2.trans
    unfold queryRawHistoryInputsBitBudget
    dsimp only
    gcongr

theorem queryOrderedHistoryInputsWithWork_length {M n : ℕ}
    (inputs : List (Fin M × ℕ × TargetInterval n)) :
    (queryOrderedHistoryInputsWithWork inputs).1.length ≤ inputs.length := by
  rw [queryOrderedHistoryInputsWithWork_value, orderedInputs_length]
  exact List.toFinset_card_le _

def queryEarlierInputsBitBudget (M P F exponent history B R : ℕ) : ℕ :=
  let count := queryEarlierRepresentativesLength P F exponent B
  queryEarlierRepresentativesBitBudget P F exponent B R +
    queryRawHistoryInputsBitBudget M P history count B +
    (queryHistoryInputsLength M P history count + 1) ^ 2 * (2002000 * (B + 1) ^ 2) + 2

theorem queryEarlierInputsWithWork_bounds {nx ny : ℕ} (M N P F exponent history B R : ℕ)
    (parent : TargetInterval nx) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (ht : Nat.size history ≤ B) (he : exponent + 1 ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, (initial r).1.width ≤ B) (hR : ∀ r, (initial r).2 ≤ R)
    (hw : 0 ≤ (initial q).1.value) (hPd : ∃ e : ℕ, P = 2 ^ e) :
    (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).1.length ≤
      queryHistoryInputsLength M P history (queryEarlierRepresentativesLength P F exponent B) ∧
    (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).2 ≤
      queryEarlierInputsBitBudget M P F exponent history B R := by
  let representatives := queryEarlierRepresentativesWithWork N P F exponent hP a initial q
  let raw := queryRawHistoryInputsWithWork M parent P history representatives.1
  let count := queryEarlierRepresentativesLength P F exponent B
  have hr := queryEarlierRepresentativesWithWork_bounds N P F exponent B R hP a initial q
    hB hN hF hFpos hPb hny he ha hi hR hw hPd
  have hraw := queryRawHistoryInputsWithWork_dyadic_bounds M N P history count B parent hP
    representatives.1 hr.1
    (fun br hb => queryEarlierRepresentativesWithWork_scale N P F exponent hP a initial q R hR br hb)
    hN hnx hny hM hPb
  have hsort := queryOrderedHistoryInputsWithWork_cost raw.1 B hM hny (fun input hin =>
    (Nat.size_le_size (queryRawHistoryInputsWithWork_time M parent P history hP
      representatives.1 input hin).le).trans ht)
  have hsort' := hsort.trans (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_left (Nat.add_le_add_right hraw.1 1) 2))
  constructor
  · simpa only [queryEarlierInputsWithWork] using
      (queryOrderedHistoryInputsWithWork_length raw.1).trans hraw.1
  · simpa only [queryEarlierInputsWithWork, queryEarlierInputsBitBudget] using
      Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hr.2 hraw.2) hsort') 2

end EditApproximation.BinaryFraction

end OAI
