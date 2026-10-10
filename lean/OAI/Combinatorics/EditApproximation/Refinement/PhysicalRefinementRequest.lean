import OAI.Combinatorics.EditApproximation.Geometry.LocalRefinementQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Concrete current and earlier child requests for refinement. The
history reader is total, with unused future times returning zero; the
local program only asks times below the current one. -/

namespace EditApproximation

theorem wideEarlierInputCover_time {nx ny M : ℕ} (parent : TargetInterval nx)
    (P history : ℕ) (representatives : List (ℕ × TargetInterval ny))
    (input : Fin M × ℕ × TargetInterval ny)
    (hinput : input ∈ wideEarlierInputCover parent P history representatives) : input.2.1 < history := by
  obtain ⟨br, _, hinput⟩ := Finset.mem_biUnion.mp hinput
  obtain ⟨i, _, hinput⟩ := Finset.mem_biUnion.mp hinput
  obtain ⟨t, ht, hinput⟩ := Finset.mem_biUnion.mp hinput
  obtain ⟨r, _, heq⟩ := Finset.mem_image.mp hinput
  have hs := congrArg (fun input : Fin M × ℕ × TargetInterval ny => input.2.1) heq
  exact hs ▸ Finset.mem_range.mp ht





section Physical

variable {α : Type*} (source target : List α) {M J : ℕ}
  (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
  (pass copy T S t : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)

def physicalRefinementRequestQuery :
    FiniteQuery {child : PhysicalTableRequest M J target.length //
      child.combinedRank T S < (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} :=
  localRefinementStepQuery source target (physicalSourceInterval source.length node)
    N P F exponent H Q tau a eta kappa delta t parentInitial child initial draw integer q
    (physicalRefinementEarlierQuery pass copy T S t node hbelow q)
    (physicalRefinementCurrentQuery pass copy T S t node hbelow q)

theorem physicalRefinementRequestQuery_value (ht : 0 < t)
    (answer : PhysicalTableRequest M J target.length → ℚ) :
    (physicalRefinementRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t node hbelow parentInitial child initial draw integer q).value
        (fun request => answer request.val) =
    rationalLocalWideStep source target (physicalSourceInterval source.length node)
      N P F exponent Q tau a delta parentInitial child initial
      (fun i r => answer (PhysicalTableRequest.refinement pass copy (physicalChild node hbelow i) T (t - 1) r))
      (fun i r => answer (PhysicalTableRequest.refinement pass copy (physicalChild node hbelow i) T t r))
      draw
      (localOnlineCandidates source target (physicalSourceInterval source.length node)
        N P F exponent H tau a eta kappa parentInitial child initial
        (fun i s r => answer (PhysicalTableRequest.refinement pass copy (physicalChild node hbelow i) T s r))
        (t - 1) integer q) q := by
  let earlier := fun i s r => answer (PhysicalTableRequest.refinement pass copy (physicalChild node hbelow i) T s r)
  let masked := fun i s r => if s < t then earlier i s r else 0
  let current := fun i r => earlier i t r
  have he (input : Fin M × ℕ × TargetInterval target.length) :
      (physicalRefinementEarlierQuery pass copy T S t node hbelow q input).value
        (fun request => answer request.val) = masked input.1 input.2.1 input.2.2 := by
    unfold physicalRefinementEarlierQuery
    split_ifs with hs
    · simp only [FiniteQuery.value, masked, ite_eq_left hs, earlier]
    · simp only [FiniteQuery.value, masked, ite_eq_right hs]
  have hc (input : Fin M × TargetInterval target.length) :
      (physicalRefinementCurrentQuery pass copy T S t node hbelow q input).value
        (fun request => answer request.val) = current input.1 input.2 := rfl
  rw [physicalRefinementRequestQuery,
    localRefinementStepQuery_value source target (physicalSourceInterval source.length node)
      N P F exponent H Q tau a eta kappa delta t parentInitial child initial draw integer q
      _ _ _ masked current ht he hc]
  have hprev : (fun i r => masked i (t - 1) r) = fun i r => earlier i (t - 1) r := by
    funext i r
    exact ite_eq_left (by omega : t - 1 < t)
  have honline := localOnlineCandidates_congr_earlier_cover source target
    (physicalSourceInterval source.length node) N P F exponent H t tau a eta kappa
    parentInitial child initial masked earlier (t - 1) integer q (by omega)
    (fun i s r hr => ite_eq_left (wideEarlierInputCover_time _ P t _ (i, s, r) hr))
  rw [hprev, honline]

end Physical

end EditApproximation

end OAI
