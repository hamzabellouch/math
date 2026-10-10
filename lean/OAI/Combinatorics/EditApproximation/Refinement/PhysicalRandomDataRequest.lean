import OAI.Combinatorics.EditApproximation.Geometry.LocalRandomDataQuery
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementDataRequest
import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryRestriction
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A physical refinement request with source reads interleaved with ranked
table requests. The requested online range is calculated after the child
mass values are returned. -/

namespace EditApproximation

section CompleteStep

variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
  (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (q : TargetInterval target.length)



theorem physicalRandomDataRequestQuery_value (answer : PhysicalTableRequest M J target.length → ℚ)
    (sourceAnswer : σ → ℚ) (draw : CellGroupDraws M F Q)
    (integer : ℕ → TargetInterval target.length → ℕ)
    (hgroup : ∀ key, (readGroup key).value sourceAnswer = groupScalarValue draw key)
    (honline : ∀ key,
      (readInteger key (keyedOnlineSourceRange source target (physicalSourceInterval source.length node)
        P exponent H tau (fun i r => (∑ j : Fin T, answer (PhysicalTableRequest.warmup pass copy
          (physicalChild node hbelow i) j.val r)) / T) key)).value sourceAnswer =
        (integer key.1 key.2 : ℚ)) :
    let parentInitial := fun r => answer (PhysicalTableRequest.warmup pass copy node 0 r)
    let child := fun i r => (∑ j : Fin T, answer (PhysicalTableRequest.warmup pass copy
      (physicalChild node hbelow i) j.val r)) / T
    let initial := fun i r => answer (PhysicalTableRequest.warmup pass copy (physicalChild node hbelow i) 0 r)
    let children := fun i s r => answer (PhysicalTableRequest.refinement pass copy
      (physicalChild node hbelow i) T s r)
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).value (Sum.elim sourceAnswer (fun request => answer request.val)) =
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
  rw [physicalRandomDataRequestQuery,
    localRandomDataQuery_value source target (physicalSourceInterval source.length node)
      N P F exponent H Q tau a eta kappa delta t _ _ _ _ _ q _ _ _ draw integer
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
    rw [FiniteQuery.mapKeys_value]
    rfl
  · intro input
    rw [FiniteQuery.mapKeys_value]
    exact physicalRefinementMassQuery_value pass copy T S t ht node hbelow q input answer
  · intro input
    rw [FiniteQuery.mapKeys_value]
    rfl
  · intro input
    rw [FiniteQuery.mapKeys_value]
    exact he input
  · intro key
    rw [FiniteQuery.mapKeys_value]
    exact hgroup key
  · intro key
    rw [FiniteQuery.mapKeys_value]
    exact honline key
  · intro input
    rw [FiniteQuery.mapKeys_value]
    rfl

end CompleteStep

end EditApproximation

end OAI
