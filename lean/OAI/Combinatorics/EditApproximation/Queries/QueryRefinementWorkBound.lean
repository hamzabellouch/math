import OAI.Combinatorics.EditApproximation.Queries.QueryRefinementGather
import OAI.Combinatorics.EditApproximation.Queries.QueryActionInputCost

namespace OAI

/-! Composition of the seven executed refinement stages. Recursive reads,
list construction, sorting, both selectors and the final continuation are
all included in this counter. -/

namespace EditApproximation

private theorem query_sum_map_bound {κ : Type*} (xs : List κ) (f : κ → ℕ) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ C) : (xs.map f).sum ≤ xs.length * C := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

namespace BinaryFraction

def queryRefinementStagesBudget (M B readCost earlierLength earlierCost onlineLength onlineCost
    sharedLength sharedCost groupLength groupCost parentCost finishCost : ℕ) : ℕ :=
  earlierCost + earlierLength * (readCost + 3) + onlineCost + parentCost + sharedCost +
    sharedLength * (readCost + 3) + groupCost +
    queryNeededInputsBitBudget (groupLength + onlineLength) M B +
    (groupLength + onlineLength) * M * (readCost + 3) + finishCost

end BinaryFraction

section Work
variable {ι β α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (a : BinaryFraction) (t : ℕ)
  (initial : TargetInterval target.length → BinaryFraction × ℕ)
  (draw : CountedCellGroupDraws M F Q) (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (online : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) × ℕ)
  (selected : List (Fin M × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) × ℕ)
  (next : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (Fin M × TargetInterval target.length) → List BinaryFraction → BitQuery ι β)

theorem queryRefinementGather_work_bound (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (B W EL EC OL OC SL SC groupLen GC FC PC : ℕ)
    (hMb : Nat.size M ≤ B) (hny : Nat.size target.length ≤ B) :
    let earlier := BinaryFraction.queryEarlierInputsWithWork M parent N P F exponent t hP a initial q
    let earlierWords := earlier.1.map fun key => (readEarlier key).value oracle
    let actions := online earlier.1 earlierWords
    let shared := BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF
      parent a (initial q).1 q draw
    let sharedWords := shared.1.map fun key => (readCurrent key).value oracle
    let groups := selected shared.1 sharedWords
    let current := queryNeededInputsWithWork groups.1 actions.1
    let currentWords := current.1.map fun key => (readCurrent key).value oracle
    earlier.1.length ≤ EL → earlier.2 ≤ EC → actions.1.length ≤ OL → actions.2 ≤ OC →
    shared.1.length ≤ SL → shared.2 ≤ SC → groups.1.length ≤ groupLen → groups.2 ≤ GC →
    (∀ key ∈ earlier.1, (readEarlier key).work oracle readWork ≤ W) →
    (∀ key, (readCurrent key).work oracle readWork ≤ W) →
    (next earlier.1 earlierWords groups.1 actions.1 current.1 currentWords).work oracle readWork ≤ FC →
    (initial q).2 ≤ PC →
    (queryRefinementGather source target parent N P F exponent Q eM eF hP hM hF
      a t initial draw q readEarlier readCurrent online selected next).work oracle readWork ≤
      BinaryFraction.queryRefinementStagesBudget M B W EL EC OL OC SL SC groupLen GC PC FC := by
  let earlier := BinaryFraction.queryEarlierInputsWithWork M parent N P F exponent t hP a initial q
  let earlierWords := earlier.1.map fun key => (readEarlier key).value oracle
  let actions := online earlier.1 earlierWords
  let shared := BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF
    parent a (initial q).1 q draw
  let sharedWords := shared.1.map fun key => (readCurrent key).value oracle
  let groups := selected shared.1 sharedWords
  let current := queryNeededInputsWithWork groups.1 actions.1
  let currentWords := current.1.map fun key => (readCurrent key).value oracle
  dsimp only
  intro heL heC hoL hoC hsL hsC hgL hgC heR hcR hfinish hparent
  change earlier.1.length ≤ EL at heL
  change earlier.2 ≤ EC at heC
  change actions.1.length ≤ OL at hoL
  change actions.2 ≤ OC at hoC
  change shared.1.length ≤ SL at hsL
  change shared.2 ≤ SC at hsC
  change groups.1.length ≤ groupLen at hgL
  change groups.2 ≤ GC at hgC
  change (next earlier.1 earlierWords groups.1 actions.1 current.1 currentWords).work oracle readWork ≤ FC at hfinish
  have heRead := (query_sum_map_bound earlier.1 (fun key => (readEarlier key).work oracle readWork + 3)
    (W + 3) (fun key hk => Nat.add_le_add_right (heR key hk) 3)).trans (Nat.mul_le_mul_right _ heL)
  have hsRead := (query_sum_map_bound shared.1 (fun key => (readCurrent key).work oracle readWork + 3)
    (W + 3) (fun key _ => Nat.add_le_add_right (hcR key) 3)).trans (Nat.mul_le_mul_right _ hsL)
  have hc := queryNeededInputsWithWork_bounds groups.1 actions.1 B hMb hny
  have hcL : current.1.length ≤ (groupLen + OL) * M :=
    hc.1.trans (Nat.mul_le_mul_right M (Nat.add_le_add hgL hoL))
  have hcC : current.2 ≤ queryNeededInputsBitBudget (groupLen + OL) M B := by
    apply hc.2.trans
    unfold queryNeededInputsBitBudget
    gcongr
  have hcRead := (query_sum_map_bound current.1 (fun key => (readCurrent key).work oracle readWork + 3)
    (W + 3) (fun key _ => Nat.add_le_add_right (hcR key) 3)).trans (Nat.mul_le_mul_right _ hcL)
  rw [queryRefinementGather_work]
  change earlier.2 + (earlier.1.map fun key => (readEarlier key).work oracle readWork + 3).sum +
    actions.2 + (initial q).2 + shared.2 +
    (shared.1.map fun key => (readCurrent key).work oracle readWork + 3).sum +
    groups.2 + current.2 + (current.1.map fun key => (readCurrent key).work oracle readWork + 3).sum +
    (next earlier.1 earlierWords groups.1 actions.1 current.1 currentWords).work oracle readWork ≤ _
  unfold BinaryFraction.queryRefinementStagesBudget
  omega

end Work
end EditApproximation

end OAI
