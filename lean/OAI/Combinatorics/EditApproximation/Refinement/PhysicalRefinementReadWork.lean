import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementDataRequest
import OAI.Combinatorics.EditApproximation.Geometry.RefinementDataQueryWork

namespace OAI

/-! Split the literal recursive reads by the unified table index. The
current-index reads are physical-child requests; initial data, warmup
mass and old history have strictly smaller indices. -/

namespace EditApproximation

def physicalCurrentReadWeight {M J ny : ℕ} (index : ℕ)
    (request : PhysicalTableRequest M J ny) : ℕ := if request.index = index then 1 else 0

def physicalEarlierReadWeight {M J ny : ℕ} (index : ℕ)
    (request : PhysicalTableRequest M J ny) : ℕ := if request.index < index then 1 else 0

theorem physicalRefinementWarmupRead_cost_current {M J ny : ℕ} (pass copy T S t : ℕ)
    (ht : 0 < t) (node : PhysicalNode M J) (q : TargetInterval ny)
    (otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : TargetInterval ny) (oracle) :
    (physicalRefinementWarmupRead pass copy T S t ht node q otherNode hnode j hj r).cost
      oracle (fun request => physicalCurrentReadWeight (T + t) request.val) = 0 := by
  have hne : j ≠ T + t := by omega
  simp only [physicalRefinementWarmupRead, FiniteQuery.cost, physicalCurrentReadWeight,
    PhysicalTableRequest.warmup, ite_eq_right hne, Nat.add_zero]

theorem physicalRefinementWarmupRead_cost_earlier {M J ny : ℕ} (pass copy T S t : ℕ)
    (ht : 0 < t) (node : PhysicalNode M J) (q : TargetInterval ny)
    (otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : TargetInterval ny) (oracle) :
    (physicalRefinementWarmupRead pass copy T S t ht node q otherNode hnode j hj r).cost
      oracle (fun request => physicalEarlierReadWeight (T + t) request.val) = 1 := by
  have hlt : j < T + t := by omega
  simp only [physicalRefinementWarmupRead, FiniteQuery.cost, physicalEarlierReadWeight,
    PhysicalTableRequest.warmup, ite_eq_left hlt, Nat.add_zero]

theorem physicalRefinementMassQuery_cost_current {M J ny : ℕ} (pass copy T S t : ℕ)
    (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (q : TargetInterval ny) (input : Fin M × TargetInterval ny) (oracle) :
    (physicalRefinementMassQuery pass copy T S t ht node hbelow q input).cost
      oracle (fun request => physicalCurrentReadWeight (T + t) request.val) = 0 := by
  simp only [physicalRefinementMassQuery, FiniteQuery.cost_collect, FiniteQuery.cost,
    physicalRefinementWarmupRead_cost_current, List.map_ofFn, Function.comp_def,
    List.sum_ofFn, Finset.sum_const_zero, Nat.add_zero]

theorem physicalRefinementMassQuery_cost_earlier {M J ny : ℕ} (pass copy T S t : ℕ)
    (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (q : TargetInterval ny) (input : Fin M × TargetInterval ny) (oracle) :
    (physicalRefinementMassQuery pass copy T S t ht node hbelow q input).cost
      oracle (fun request => physicalEarlierReadWeight (T + t) request.val) = T := by
  simp only [physicalRefinementMassQuery, FiniteQuery.cost_collect, FiniteQuery.cost,
    physicalRefinementWarmupRead_cost_earlier, List.map_ofFn, Function.comp_def,
    List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Nat.mul_one, Nat.add_zero]

theorem physicalRefinementCurrentQuery_cost_current {M J ny : ℕ} (pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval ny)
    (input : Fin M × TargetInterval ny) (oracle) :
    (physicalRefinementCurrentQuery pass copy T S t node hbelow q input).cost
      oracle (fun request => physicalCurrentReadWeight (T + t) request.val) = 1 := by
  simp only [physicalRefinementCurrentQuery, FiniteQuery.cost, physicalCurrentReadWeight,
    PhysicalTableRequest.refinement, ite_true, Nat.add_zero]

theorem physicalRefinementCurrentQuery_cost_earlier {M J ny : ℕ} (pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval ny)
    (input : Fin M × TargetInterval ny) (oracle) :
    (physicalRefinementCurrentQuery pass copy T S t node hbelow q input).cost
      oracle (fun request => physicalEarlierReadWeight (T + t) request.val) = 0 := by
  simp only [physicalRefinementCurrentQuery, FiniteQuery.cost, physicalEarlierReadWeight,
    PhysicalTableRequest.refinement, lt_self_iff_false, ite_false, Nat.add_zero]

theorem physicalRefinementEarlierQuery_cost_current {M J ny : ℕ} (pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval ny)
    (input : Fin M × ℕ × TargetInterval ny) (oracle) :
    (physicalRefinementEarlierQuery pass copy T S t node hbelow q input).cost
      oracle (fun request => physicalCurrentReadWeight (T + t) request.val) = 0 := by
  unfold physicalRefinementEarlierQuery
  split_ifs with hs
  · have hne : T + input.2.1 ≠ T + t := by omega
    simp only [FiniteQuery.cost, physicalCurrentReadWeight, PhysicalTableRequest.refinement,
      hne, ↓reduceIte, Nat.add_zero]
  · rfl

theorem physicalRefinementEarlierQuery_cost_earlier {M J ny : ℕ} (pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval ny)
    (input : Fin M × ℕ × TargetInterval ny) (oracle) :
    (physicalRefinementEarlierQuery pass copy T S t node hbelow q input).cost
      oracle (fun request => physicalEarlierReadWeight (T + t) request.val) ≤ 1 := by
  unfold physicalRefinementEarlierQuery
  split_ifs with hs
  · have hlt : T + input.2.1 < T + t := by omega
    simp only [FiniteQuery.cost, physicalEarlierReadWeight, PhysicalTableRequest.refinement,
      hlt, ↓reduceIte, Nat.add_zero, le_refl]
  · exact Nat.zero_le 1

private def physicalReadMaskedAnswers {M J ny : ℕ}
    (pass copy T t : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (answer : PhysicalTableRequest M J ny → ℚ) (i : Fin M) (s : ℕ)
    (r : TargetInterval ny) : ℚ :=
  if s < t then answer (PhysicalTableRequest.refinement pass copy
    (physicalChild node hbelow i) T s r) else 0

section Full

variable {α : Type*} (source target : List α) {M J : ℕ}
  (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
  (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length) (answer : PhysicalTableRequest M J target.length → ℚ)

local notation "requestType" => {child : PhysicalTableRequest M J target.length //
  PhysicalTableRequest.combinedRank T S child <
    PhysicalTableRequest.combinedRank T S (PhysicalTableRequest.refinement pass copy node T t q)}
local notation "oracle" => (fun request : requestType => answer (Subtype.val request))
local notation "parentInitial" => (fun r => answer (PhysicalTableRequest.warmup pass copy node 0 r))
local notation "childMass" => (fun (i : Fin M) (r : TargetInterval target.length) =>
  (∑ j : Fin T, answer (PhysicalTableRequest.warmup pass copy
    (physicalChild node hbelow i) (Fin.val j) r)) / T)
local notation "childInitial" => (fun i r => answer (PhysicalTableRequest.warmup pass copy
  (physicalChild node hbelow i) 0 r))
local notation "masked" => physicalReadMaskedAnswers pass copy T t node hbelow answer
local notation "current" => (fun i r => answer (PhysicalTableRequest.refinement pass copy
  (physicalChild node hbelow i) T t r))
local notation "program" => physicalRefinementDataRequestQuery source target N P F exponent H Q
  tau a eta kappa delta pass copy T S t ht node hbelow draw integer q
local notation "parentRead" => physicalRefinementWarmupRead pass copy T S t ht node q node le_rfl 0 (Nat.zero_le T)
local notation "massRead" => physicalRefinementMassQuery pass copy T S t ht node hbelow q
local notation "initialRead" => (fun input : Fin M × TargetInterval target.length =>
  physicalRefinementWarmupRead pass copy T S t ht node q (physicalChild node hbelow (Prod.fst input))
    (Nat.le_succ (Fin.val (Sigma.fst node)))
    0 (Nat.zero_le T) (Prod.snd input))
local notation "earlierRead" => physicalRefinementEarlierQuery pass copy T S t node hbelow q
local notation "currentRead" => physicalRefinementCurrentQuery pass copy T S t node hbelow q
local notation "currentCover" => currentQueryInputCover source target (physicalSourceInterval source.length node)
  N P F exponent Q tau a parentInitial childMass childInitial current draw q
  (localOnlineCandidates source target (physicalSourceInterval source.length node)
    N P F exponent H tau a eta kappa parentInitial childMass childInitial masked (t - 1) integer q)

theorem physicalRefinementDataRequest_cost_le (weight : requestType → ℕ)
    (parentCost massCost initialCost earlierCost currentCost : ℕ)
    (hparent : ∀ r, (parentRead r).cost oracle weight ≤ parentCost)
    (hmass : ∀ input, (massRead input).cost oracle weight ≤ massCost)
    (hinitial : ∀ input, (initialRead input).cost oracle weight ≤ initialCost)
    (hearlier : ∀ input, (earlierRead input).cost oracle weight ≤ earlierCost)
    (hcurrent : ∀ input, (currentRead input).cost oracle weight ≤ currentCost) :
    (program).cost oracle weight ≤
      (1 + (refinementInitialSupport N P F exponent a (parentInitial q) q).length) * parentCost +
      (refinementBandInputList (M := M) (physicalSourceInterval source.length node)
        N P F exponent a parentInitial q).length * (massCost + initialCost) +
      (queryEarlierInputCover (M := M) (physicalSourceInterval source.length node)
        N P F exponent t a parentInitial q).card * earlierCost +
      2 * (currentCover).card * currentCost := by
  have hreadEarlier (input : Fin M × ℕ × TargetInterval target.length) :
      (earlierRead input).value oracle = masked input.1 input.2.1 input.2.2 := by
    unfold physicalRefinementEarlierQuery physicalReadMaskedAnswers
    split_ifs with hs <;> rfl
  exact localRefinementDataQuery_cost_le source target (physicalSourceInterval source.length node)
    N P F exponent H Q tau a eta kappa delta t parentRead massRead initialRead draw integer q
    earlierRead currentRead oracle weight parentInitial childMass childInitial masked current ht
    (fun _ => rfl) (fun input => physicalRefinementMassQuery_value pass copy T S t ht node hbelow q input answer)
    (fun _ => rfl) hreadEarlier (fun _ => rfl)
    parentCost massCost initialCost earlierCost currentCost hparent hmass hinitial hearlier hcurrent

theorem physicalRefinementDataRequest_current_reads :
    (program).cost oracle (fun request => physicalCurrentReadWeight (T + t) request.val) ≤
      2 * (currentCover).card := by
  have h := physicalRefinementDataRequest_cost_le source target N P F exponent H Q tau a eta kappa delta
    pass copy T S t ht node hbelow draw integer q answer
    (fun request => physicalCurrentReadWeight (T + t) request.val) 0 0 0 0 1
    (fun r => (physicalRefinementWarmupRead_cost_current pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r oracle).le)
    (fun input => (physicalRefinementMassQuery_cost_current pass copy T S t ht node hbelow q input oracle).le)
    (fun input => (physicalRefinementWarmupRead_cost_current pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 oracle).le)
    (fun input => (physicalRefinementEarlierQuery_cost_current pass copy T S t node hbelow q input oracle).le)
    (fun input => (physicalRefinementCurrentQuery_cost_current pass copy T S t node hbelow q input oracle).le)
  simpa only [Nat.add_zero, Nat.mul_zero, Nat.zero_add, Nat.mul_one] using h

theorem physicalRefinementDataRequest_earlier_reads :
    (program).cost oracle (fun request => physicalEarlierReadWeight (T + t) request.val) ≤
      1 + (refinementInitialSupport N P F exponent a (parentInitial q) q).length +
      (refinementBandInputList (M := M) (physicalSourceInterval source.length node)
        N P F exponent a parentInitial q).length * (T + 1) +
      (queryEarlierInputCover (M := M) (physicalSourceInterval source.length node)
        N P F exponent t a parentInitial q).card := by
  have h := physicalRefinementDataRequest_cost_le source target N P F exponent H Q tau a eta kappa delta
    pass copy T S t ht node hbelow draw integer q answer
    (fun request => physicalEarlierReadWeight (T + t) request.val) 1 T 1 1 0
    (fun r => (physicalRefinementWarmupRead_cost_earlier pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r oracle).le)
    (fun input => (physicalRefinementMassQuery_cost_earlier pass copy T S t ht node hbelow q input oracle).le)
    (fun input => (physicalRefinementWarmupRead_cost_earlier pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 oracle).le)
    (fun input => physicalRefinementEarlierQuery_cost_earlier pass copy T S t node hbelow q input oracle)
    (fun input => (physicalRefinementCurrentQuery_cost_earlier pass copy T S t node hbelow q input oracle).le)
  simpa only [Nat.mul_one, Nat.mul_zero, Nat.add_zero] using h

end Full

theorem physicalRefinementWarmupRead_keys_bounded {M J ny : ℕ}
    (passes copies pass copy T S t : ℕ) (ht : 0 < t)
    (hpass : pass < passes) (hcopy : copy < copies)
    (node : PhysicalNode M J) (q : TargetInterval ny)
    (otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : TargetInterval ny) (oracle) :
    ∀ key ∈ (physicalRefinementWarmupRead pass copy T S t ht node q otherNode hnode j hj r).keys oracle,
      key.val.Bounded passes copies T S := by
  intro key hk
  simp only [physicalRefinementWarmupRead, FiniteQuery.keys, List.mem_singleton] at hk
  subst key
  exact PhysicalTableRequest.warmup_bounded passes copies pass copy otherNode T S j r hpass hcopy hj

theorem physicalRefinementDataRequest_keys_bounded {α : Type*} (source target : List α) {M J : ℕ}
    (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
    (passes copies pass copy T S t : ℕ) (ht : 0 < t) (htS : t ≤ S)
    (hpass : pass < passes) (hcopy : copy < copies)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (q : TargetInterval target.length) (oracle) :
    ∀ key ∈ (physicalRefinementDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow draw integer q).keys oracle,
      key.val.Bounded passes copies T S := by
  unfold physicalRefinementDataRequestQuery
  apply localRefinementDataQuery_keys_all
  · intro r key hk
    exact physicalRefinementWarmupRead_keys_bounded passes copies pass copy T S t ht hpass hcopy
      node q node le_rfl 0 (Nat.zero_le T) r oracle key hk
  · intro input
    unfold physicalRefinementMassQuery
    apply FiniteQuery.keys_all_collect
    · intro j _ key hk
      exact physicalRefinementWarmupRead_keys_bounded passes copies pass copy T S t ht hpass hcopy
        node q (physicalChild node hbelow input.1) _ j.val (Nat.le_of_lt j.isLt) input.2 oracle key hk
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro input key hk
    exact physicalRefinementWarmupRead_keys_bounded passes copies pass copy T S t ht hpass hcopy
      node q (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 oracle key hk
  · intro input key hk
    unfold physicalRefinementEarlierQuery at hk
    split_ifs at hk with hs
    · simp only [FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact PhysicalTableRequest.refinement_bounded passes copies pass copy
        (physicalChild node hbelow input.1) T S input.2.1 input.2.2 hpass hcopy (by omega)
    · exact False.elim (List.not_mem_nil hk)
  · intro input key hk
    simp only [physicalRefinementCurrentQuery, FiniteQuery.keys, List.mem_singleton] at hk
    subst key
    exact PhysicalTableRequest.refinement_bounded passes copies pass copy
      (physicalChild node hbelow input.1) T S t input.2 hpass hcopy htS

end EditApproximation

end OAI
