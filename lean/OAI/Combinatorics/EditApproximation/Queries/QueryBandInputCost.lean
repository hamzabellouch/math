import OAI.Combinatorics.EditApproximation.Queries.QueryRepresentativeCost
import OAI.Combinatorics.EditApproximation.Queries.QueryRepresentativeScales
import OAI.Combinatorics.EditApproximation.Queries.QueryWideBounds

namespace OAI

namespace EditApproximation.BinaryFraction

def queryWideInputsBitBudget (M P count B : ℕ) : ℕ :=
  let G := (40 * P + 2) ^ 2
  let C := wideChildGridBitBudget P (B + 1)
  count * (M * (C + 4 * G + 1 + G + 3) + M * G + 3) +
    (count * (M * G) + 1) ^ 2 * (24 * B + 12) + M + 2

theorem queryWideInputsWithWork_dyadic_bounds {nx ny : ℕ}
    (M N P count B : ℕ) (parent : TargetInterval nx) (hP : 0 < P)
    (representatives : List (ℕ × TargetInterval ny))
    (hl : representatives.length ≤ count)
    (hs : ∀ br ∈ representatives, br.1 ∈ dyadicScales N)
    (hN : Nat.size N ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hPb : Nat.size P ≤ B) :
    (queryWideInputsWithWork M parent P representatives).1.length ≤ count * (M * (40 * P + 2) ^ 2) ∧
    (queryWideInputsWithWork M parent P representatives).2 ≤ queryWideInputsBitBudget M P count B := by
  have hb := queryWideInputsWithWork_bounds M parent P representatives ((40 * P + 2) ^ 2)
    (wideChildGridBitBudget P (B + 1)) B hM hny
    (fun br _ i => by rw [wideChildGridWithWork_value _ _ _ _ _ hP]; exact wideChildStateList_length_le parent br.2 hP i)
    (fun br hbr i => wideChildGridWithWork_cost parent br.2 br.1 P (B + 1) i hP
      (by omega) (by omega) (by omega)
      ((dyadicScales_size_bound N br.1 (hs br hbr)).trans (by omega)) (by omega))
  constructor
  · exact hb.1.trans (Nat.mul_le_mul_right _ hl)
  · apply hb.2.trans
    unfold queryWideInputsBitBudget
    dsimp only
    gcongr

def queryBandInputsBitBudget (M P F exponent B R : ℕ) : ℕ :=
  queryEarlierRepresentativesBitBudget P F exponent B R +
    queryWideInputsBitBudget M P (queryEarlierRepresentativesLength P F exponent B) B + 1

theorem queryBandInputsWithWork_bounds {nx ny : ℕ} (M N P F exponent B R : ℕ)
    (parent : TargetInterval nx) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (he : exponent + 1 ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, (initial r).1.width ≤ B) (hR : ∀ r, (initial r).2 ≤ R)
    (hw : 0 ≤ (initial q).1.value) (hPd : ∃ e : ℕ, P = 2 ^ e) :
    (queryBandInputsWithWork M parent N P F exponent hP a initial q).1.length ≤
      queryEarlierRepresentativesLength P F exponent B * (M * (40 * P + 2) ^ 2) ∧
    (queryBandInputsWithWork M parent N P F exponent hP a initial q).2 ≤
      queryBandInputsBitBudget M P F exponent B R := by
  have hr := queryEarlierRepresentativesWithWork_bounds N P F exponent B R hP a initial q
    hB hN hF hFpos hPb hny he ha hi hR hw hPd
  have hwide := queryWideInputsWithWork_dyadic_bounds M N P
    (queryEarlierRepresentativesLength P F exponent B) B parent hP
    (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1 hr.1
    (fun br hb => queryEarlierRepresentativesWithWork_scale N P F exponent hP a initial q R hR br hb)
    hN hnx hny hM hPb
  constructor
  · simpa only [queryBandInputsWithWork] using hwide.1
  · simpa only [queryBandInputsWithWork, queryBandInputsBitBudget] using
      Nat.add_le_add_right (Nat.add_le_add hr.2 hwide.2) 1

end EditApproximation.BinaryFraction

end OAI
