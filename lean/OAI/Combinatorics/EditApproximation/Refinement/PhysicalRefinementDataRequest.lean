import OAI.Combinatorics.EditApproximation.Geometry.RefinementDataQuery
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementRequest
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! All initial and warmup-mass data are ordinary earlier table
requests. A positive refinement step therefore has no fixed-table oracle
arguments. Parent initial data use the same node's warmup-zero entry;
child data and histories use the concrete physical children. -/

namespace EditApproximation

theorem physicalInitialQuery_value_local {ι α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (seedRead : PhysicalEntry M J target.length → FiniteQuery ι)
    (oracle : ι → ℚ) (U : PhysicalEntry M J target.length → ℕ)
    (node : PhysicalNode M J) (q : TargetInterval target.length)
    (hseed : ∀ r, (seedRead (node, r)).value oracle = (U (node, r) : ℚ)) :
    (physicalInitialQuery source target N P F A seedRead (node, q)).value oracle =
      stageInitial source target U N P F A (node, q) := by
  unfold physicalInitialQuery stageInitial physicalInitialTable
  dsimp only
  split_ifs with hleaf
  · rfl
  · rw [FiniteQuery.bind_value, hseed q]
    simp only [Nat.ceil_natCast]
    rw [FiniteQuery.collect_value]
    simp only [hseed, FiniteQuery.value]
    symm
    apply localInitialConeTable_congr_raw
    · simp only [ite_true]
    · intro r hr
      by_cases heq : r = q
      · subst r
        simp only [ite_true]
      · rw [ite_eq_right heq, finiteAnswerTable_map _ _ r hr, Nat.ceil_natCast]

theorem physicalWarmupStepQuery_value_local {ι α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (seedRead : PhysicalEntry M J target.length → FiniteQuery ι)
    (childRead : Fin M × TargetInterval target.length → FiniteQuery ι) (oracle : ι → ℚ)
    (U : PhysicalEntry M J target.length → ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (t : ℕ) (q : TargetInterval target.length)
    (hseed : ∀ r, (seedRead (node, r)).value oracle = (U (node, r) : ℚ))
    (hchild : ∀ input, (childRead input).value oracle =
      physicalLocalWarmup source target U N P F A t (physicalChild node hbelow input.1, input.2)) :
    (physicalWarmupStepQuery source target N P F A seedRead childRead node q).value oracle =
      physicalLocalWarmup source target U N P F A (t + 1) (node, q) := by
  rw [physicalLocalWarmup]
  simp only [dite_eq_left hbelow, ite_eq_right hleaf]
  exact localWarmupStepQuery_value _ N P F (refinementFactor A F) _ _ oracle _ _
    (fun r => physicalInitialQuery_value_local source target N P F A seedRead oracle U node r hseed)
    hchild q

theorem physicalWarmupRequestQuery_value_local {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (pass copy T S j : ℕ) (node : PhysicalNode M J) (q : TargetInterval target.length)
    (seedRead : PhysicalEntry M J target.length →
      FiniteQuery {child : PhysicalTableRequest M J target.length //
        child.combinedRank T S < (PhysicalTableRequest.warmup pass copy node j q).combinedRank T S})
    (values : PhysicalTableRequest M J target.length → ℚ)
    (U : PhysicalEntry M J target.length → ℕ)
    (hseed : ∀ r, (seedRead (node, r)).value (fun child => values child.val) = (U (node, r) : ℚ))
    (hchild : ∀ (hbelow : node.1.val < J) (input : Fin M × TargetInterval target.length),
      values (PhysicalTableRequest.warmup pass copy (physicalChild node hbelow input.1) (j - 1) input.2) =
        physicalLocalWarmup source target U N P F A (j - 1)
          (physicalChild node hbelow input.1, input.2)) :
    (physicalWarmupRequestQuery source target N P F A pass copy T S j node q seedRead).value
      (fun child => values child.val) = physicalLocalWarmup source target U N P F A j (node, q) := by
  cases j with
  | zero => exact physicalInitialQuery_value_local source target N P F A seedRead _ U node q hseed
  | succ t =>
    dsimp only [physicalWarmupRequestQuery]
    split_ifs with hbelow hleaf
    · rw [physicalLocalWarmup]
      simp only [dite_eq_left hbelow, ite_eq_left hleaf]
      exact physicalInitialQuery_value_local source target N P F A seedRead _ U node q hseed
    · apply physicalWarmupStepQuery_value_local source target N P F A seedRead _ _ U
        node hbelow hleaf t q hseed
      intro input
      exact hchild hbelow input
    · rw [physicalLocalWarmup]
      simp only [dite_eq_right hbelow]
      exact physicalInitialQuery_value_local source target N P F A seedRead _ U node q hseed





theorem physicalRefinementMassQuery_value {M J ny : ℕ} (pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval ny)
    (input : Fin M × TargetInterval ny) (answer : PhysicalTableRequest M J ny → ℚ) :
    (physicalRefinementMassQuery pass copy T S t ht node hbelow q input).value
      (fun request => answer request.val) =
      (∑ j : Fin T, answer (PhysicalTableRequest.warmup pass copy
        (physicalChild node hbelow input.1) j.val input.2)) / T := by
  simp only [physicalRefinementMassQuery, FiniteQuery.collect_value, physicalRefinementWarmupRead,
    FiniteQuery.value, List.map_ofFn, List.sum_ofFn, Function.comp_def]

section CompleteStep

variable {α : Type*} (source target : List α) {M J : ℕ}
  (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
  (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)

def physicalRefinementDataRequestQuery :
    FiniteQuery {child : PhysicalTableRequest M J target.length //
      child.combinedRank T S < (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} :=
  localRefinementDataQuery source target (physicalSourceInterval source.length node)
    N P F exponent H Q tau a eta kappa delta t
    (physicalRefinementWarmupRead pass copy T S t ht node q node le_rfl 0 (Nat.zero_le T))
    (physicalRefinementMassQuery pass copy T S t ht node hbelow q)
    (fun input => physicalRefinementWarmupRead pass copy T S t ht node q
      (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
      0 (Nat.zero_le T) input.2)
    draw integer q (physicalRefinementEarlierQuery pass copy T S t node hbelow q)
    (physicalRefinementCurrentQuery pass copy T S t node hbelow q)

theorem physicalRefinementDataRequestQuery_value (answer : PhysicalTableRequest M J target.length → ℚ) :
    let parentInitial := fun r => answer (PhysicalTableRequest.warmup pass copy node 0 r)
    let child := fun i r => (∑ j : Fin T, answer (PhysicalTableRequest.warmup pass copy
      (physicalChild node hbelow i) j.val r)) / T
    let initial := fun i r => answer (PhysicalTableRequest.warmup pass copy (physicalChild node hbelow i) 0 r)
    let children := fun i s r => answer (PhysicalTableRequest.refinement pass copy
      (physicalChild node hbelow i) T s r)
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow draw integer q).value (fun request => answer request.val) =
      rationalLocalWideStep source target (physicalSourceInterval source.length node)
        N P F exponent Q tau a delta parentInitial child initial
        (fun i r => children i (t - 1) r) (fun i r => children i t r) draw
        (localOnlineCandidates source target (physicalSourceInterval source.length node)
          N P F exponent H tau a eta kappa parentInitial child initial children (t - 1) integer q) q := by
  dsimp only
  let earlier := fun i s r => answer (PhysicalTableRequest.refinement pass copy (physicalChild node hbelow i) T s r)
  let masked := fun i s r => if s < t then earlier i s r else 0
  let parentInitial := fun r => answer (PhysicalTableRequest.warmup pass copy node 0 r)
  let child := fun i r => (∑ j : Fin T, answer (PhysicalTableRequest.warmup pass copy
    (physicalChild node hbelow i) j.val r)) / T
  let initial := fun i r => answer (PhysicalTableRequest.warmup pass copy (physicalChild node hbelow i) 0 r)
  have he (input : Fin M × ℕ × TargetInterval target.length) :
      (physicalRefinementEarlierQuery pass copy T S t node hbelow q input).value
        (fun request => answer request.val) = masked input.1 input.2.1 input.2.2 := by
    unfold physicalRefinementEarlierQuery
    split_ifs with hs
    · simp only [FiniteQuery.value, masked, ite_eq_left hs, earlier]
    · simp only [FiniteQuery.value, masked, ite_eq_right hs]
  rw [physicalRefinementDataRequestQuery,
    localRefinementDataQuery_value source target (physicalSourceInterval source.length node)
      N P F exponent H Q tau a eta kappa delta t _ _ _ draw integer q _ _ _
      parentInitial child initial masked (fun i r => earlier i t r) ht]
  · have hprev : (fun i r => masked i (t - 1) r) = fun i r => earlier i (t - 1) r := by
      funext i r
      exact ite_eq_left (by omega : t - 1 < t)
    have honline := localOnlineCandidates_congr_earlier_cover source target
      (physicalSourceInterval source.length node) N P F exponent H t tau a eta kappa
      parentInitial child initial masked earlier (t - 1) integer q (by omega)
      (fun i s r hr => ite_eq_left (wideEarlierInputCover_time _ P t _ (i, s, r) hr))
    rw [hprev, honline]
  · intro r
    rfl
  · intro input
    exact physicalRefinementMassQuery_value pass copy T S t ht node hbelow q input answer
  · intro input
    rfl
  · exact he
  · intro input
    rfl

end CompleteStep

end EditApproximation

end OAI
