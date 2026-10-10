import OAI.Combinatorics.EditApproximation.Queries.QueryDataBuffers
import OAI.Combinatorics.EditApproximation.Binary.BinaryContinuationReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The final local continuation consumes the two gathered data buffers.
It recomputes the local representative list with counted initial reads and
runs the Boolean Bellman/online minima on the already selected actions. -/

namespace EditApproximation
namespace BinaryFraction

section Finish
variable {nx ny M : ℕ} (parent : TargetInterval nx) (N P F : ℕ)
  (a delta : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ)
  (t : ℕ) (earlierKeys : List (Fin M × ℕ × TargetInterval ny)) (earlierWords : List BinaryFraction)
  (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
  (currentKeys : List (Fin M × TargetInterval ny)) (currentWords : List BinaryFraction)
  (query : TargetInterval ny)



theorem queryRefinementFinishWithWork_value (hP : 0 < P)
    (R : ℕ) (hp : ∀ r, (initial r).2 ≤ R)
    (he : ∀ input, (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).2 ≤ R)
    (hc : ∀ i r, (queryChildReadWithWork currentKeys currentWords i r).2 ≤ R) :
    (queryRefinementFinishWithWork parent N P F a delta initial t earlierKeys earlierWords
      groups online currentKeys currentWords query).1.value =
      rationalWideStep parent
        (localRefinementRepresentatives N P F a.value (fun r => (initial r).1.value) query)
        P (fun _ => (initial query).1.value) (128 * F) delta.value
        (fun input => finiteAnswerTable earlierKeys (earlierWords.map value) (input.1, t - 1, input.2))
        (finiteAnswerTable currentKeys (currentWords.map value))
        (groups.map BinaryBellmanAction.decode) (online.map BinaryBellmanAction.decode) query := by
  have hr := (localRepresentativeReadWithWork_eq_cost N P F a initial query R hp).1
  have hv := (physicalContinuationReadWithWork_eq_cost parent
    (localRepresentativeReadWithWork N P F a initial query).1 P F delta (initial query).1
    (queryHistoryReadWithWork earlierKeys earlierWords (t - 1))
    (fun input => queryChildReadWithWork currentKeys currentWords input.1 input.2)
    groups online query R he (fun input => hc input.1 input.2)).1
  simp only [queryRefinementFinishWithWork]
  rw [hv, hr, physicalContinuationWithWork_value parent
    (localRepresentativesWithWork N P F a (fun r => (initial r).1) query).1 P F delta
    (initial query).1 (fun input => (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).1)
    (fun input => (queryChildReadWithWork currentKeys currentWords input.1 input.2).1)
    groups online query hP]
  simp only [localRepresentativesWithWork_value N P F hP a (fun r => (initial r).1) query,
    queryHistoryReadWithWork_value, queryChildReadWithWork_value]


theorem queryRefinementFinishWithWork_value_only (hP : 0 < P) :
    (queryRefinementFinishWithWork parent N P F a delta initial t earlierKeys earlierWords
      groups online currentKeys currentWords query).1.value =
      rationalWideStep parent
        (localRefinementRepresentatives N P F a.value (fun r => (initial r).1.value) query)
        P (fun _ => (initial query).1.value) (128 * F) delta.value
        (fun input => finiteAnswerTable earlierKeys (earlierWords.map value) (input.1, t - 1, input.2))
        (finiteAnswerTable currentKeys (currentWords.map value))
        (groups.map BinaryBellmanAction.decode) (online.map BinaryBellmanAction.decode) query := by
  classical
  let p := ∑ r, (initial r).2
  let e := ∑ input : Fin M × TargetInterval ny,
    (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).2
  let c := ∑ input : Fin M × TargetInterval ny,
    (queryChildReadWithWork currentKeys currentWords input.1 input.2).2
  apply queryRefinementFinishWithWork_value parent N P F a delta initial t earlierKeys earlierWords
    groups online currentKeys currentWords query hP (p + e + c)
  · intro r
    have h : (initial r).2 ≤ p := Finset.single_le_sum (f := fun r => (initial r).2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    omega
  · intro input
    have h : (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).2 ≤ e :=
      Finset.single_le_sum (f := fun input =>
        (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ input)
    omega
  · intro i r
    have h : (queryChildReadWithWork currentKeys currentWords i r).2 ≤ c :=
      Finset.single_le_sum (f := fun input : Fin M × TargetInterval ny =>
        (queryChildReadWithWork currentKeys currentWords input.1 input.2).2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, r))
    omega

end Finish
end BinaryFraction
end EditApproximation

end OAI
