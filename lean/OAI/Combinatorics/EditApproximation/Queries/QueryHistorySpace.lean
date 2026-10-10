import OAI.Combinatorics.EditApproximation.Queries.QueryInitialSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalRepresentativeSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryInputs
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem queryEarlierRepresentativesAllocation_le_work {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ)
    (allocation : TargetInterval n → ℕ) (q : TargetInterval n)
    (h : ∀ r, allocation r ≤ (initial r).2) :
    queryEarlierRepresentativesAllocation N P F exponent hP a initial allocation q ≤
      (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).2 := by
  let build := fun key : ℕ × ℕ × ℕ =>
    let centers := cellCentersReadWithWork P F key.1 a (inversePowerTwo exponent) initial key.2
    let labeled := arithmeticMapWithWork (fun r => ((key.1, r), 1)) centers.1
    (labeled.1, centers.2 + labeled.2 + 1)
  have hq := h q
  have hr := localRepresentativeReadAllocation_le_work N P F a initial allocation q h
  have hg := queryGroupKeysAllocation_le_work N F exponent a (initial q).1 q
  have hc := arithmeticFlatMapAllocation_le_work build (fun key =>
      cellCentersReadAllocation P F key.1 a (inversePowerTwo exponent) initial allocation key.2 +
      arithmeticMapAllocation (fun _ => 1)
        (cellCentersReadWithWork P F key.1 a (inversePowerTwo exponent) initial key.2).1)
      (queryGroupKeysWithWork N F exponent a (initial q).1 q).1 (by
        intro key _
        have hh := cellCentersReadAllocation_le_work P F key.1 a (inversePowerTwo exponent) initial allocation key.2 h
        have hm := arithmeticMapAllocation_le_work (fun r => ((key.1, r), 1)) (fun _ => 1)
          (cellCentersReadWithWork P F key.1 a (inversePowerTwo exponent) initial key.2).1 (fun _ _ => le_rfl)
        dsimp only [build]
        omega)
  have ho := queryOnlineKeysAllocation_le_work N P F hP a (initial q).1 q
  unfold queryEarlierRepresentativesAllocation queryEarlierRepresentativesWithWork
  dsimp only [build] at hc ⊢
  omega



theorem queryWideInputsAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx) (P : ℕ)
    (representatives : List (ℕ × TargetInterval ny)) :
    queryWideInputsAllocation M parent P representatives ≤ (queryWideInputsWithWork M parent P representatives).2 := by
  let child := fun (br : ℕ × TargetInterval ny) (i : Fin M) =>
      let states := wideChildGridWithWork parent br.2 br.1 P i
      let labeled := arithmeticMapWithWork (fun r => ((i, r), 1)) states.1
      (labeled.1, states.2 + labeled.2 + 1)
  let one := fun (br : ℕ × TargetInterval ny) (i : Fin M) =>
    wideChildGridAllocation parent br.2 br.1 P i +
      arithmeticMapAllocation (fun _ => 1) (wideChildGridWithWork parent br.2 br.1 P i).1
  have hchild (br : ℕ × TargetInterval ny) (i : Fin M) : one br i ≤ (child br i).2 := by
    have hw := wideChildGridAllocation_le_work parent br.2 br.1 P i
    have hm := arithmeticMapAllocation_le_work (fun r => ((i, r), 1)) (fun _ => 1)
      (wideChildGridWithWork parent br.2 br.1 P i).1 (fun _ _ => le_rfl)
    dsimp only [one, child]
    omega
  have hw := arithmeticFlatMapAllocation_le_work
    (fun br => arithmeticFlatMapWithWork (child br) (List.finRange M))
    (fun br => arithmeticFlatMapAllocation (child br) (one br) (List.finRange M)) representatives
    (fun br _ => arithmeticFlatMapAllocation_le_work (child br) (one br) (List.finRange M) (fun i _ => hchild br i))
  have he := queryEraseAllocation_le_work coordinateEqualWithWork coordinateEqualAllocation
    (arithmeticFlatMapWithWork (fun br => arithmeticFlatMapWithWork (child br) (List.finRange M)) representatives).1
    coordinateEqualAllocation_le_work
  unfold queryWideInputsAllocation queryWideInputsWithWork
  dsimp only [child, one] at hw he ⊢
  omega



theorem queryRawHistoryInputsAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (P history : ℕ) (representatives : List (ℕ × TargetInterval ny)) :
    queryRawHistoryInputsAllocation M parent P history representatives ≤
      (queryRawHistoryInputsWithWork M parent P history representatives).2 := by
  let child := fun (br : ℕ × TargetInterval ny) (i : Fin M) =>
    let states := wideChildGridWithWork parent br.2 br.1 P i
    let times := arithmeticFlatMapWithWork (fun t =>
      arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1) (List.range history)
    (times.1, states.2 + times.2 + history + 2)
  let one := fun (br : ℕ × TargetInterval ny) (i : Fin M) =>
    wideChildGridAllocation parent br.2 br.1 P i + history +
      arithmeticFlatMapAllocation (fun t => arithmeticMapWithWork (fun r => ((i, t, r), 1))
        (wideChildGridWithWork parent br.2 br.1 P i).1)
        (fun _ => arithmeticMapAllocation (fun _ => 1) (wideChildGridWithWork parent br.2 br.1 P i).1)
        (List.range history)
  have hchild (br : ℕ × TargetInterval ny) (i : Fin M) : one br i ≤ (child br i).2 := by
    have hw := wideChildGridAllocation_le_work parent br.2 br.1 P i
    have ht := arithmeticFlatMapAllocation_le_work
      (fun t => arithmeticMapWithWork (fun r => ((i, t, r), 1)) (wideChildGridWithWork parent br.2 br.1 P i).1)
      (fun _ => arithmeticMapAllocation (fun _ => 1) (wideChildGridWithWork parent br.2 br.1 P i).1)
      (List.range history) (fun _ _ => arithmeticMapAllocation_le_work _ _ _ (fun _ _ => le_rfl))
    dsimp only [one, child]
    omega
  have hall := arithmeticFlatMapAllocation_le_work
    (fun br => arithmeticFlatMapWithWork (child br) (List.finRange M))
    (fun br => arithmeticFlatMapAllocation (child br) (one br) (List.finRange M)) representatives
    (fun br _ => arithmeticFlatMapAllocation_le_work (child br) (one br) (List.finRange M) (fun i _ => hchild br i))
  unfold queryRawHistoryInputsAllocation queryRawHistoryInputsWithWork
  dsimp only [child, one] at hall ⊢
  omega



theorem queryEarlierInputsAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent history : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (allocation : TargetInterval ny → ℕ)
    (q : TargetInterval ny) (h : ∀ r, allocation r ≤ (initial r).2) :
    queryEarlierInputsAllocation M parent N P F exponent history hP a initial allocation q ≤
      (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).2 := by
  have hr := queryEarlierRepresentativesAllocation_le_work N P F exponent hP a initial allocation q h
  have hw := queryRawHistoryInputsAllocation_le_work M parent P history
    (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1
  have ho := queryOrderedHistoryInputsAllocation_le_work
    (queryRawHistoryInputsWithWork M parent P history (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1).1
  unfold queryEarlierInputsAllocation queryEarlierInputsWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
