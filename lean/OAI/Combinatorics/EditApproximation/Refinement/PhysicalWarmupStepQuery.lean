import OAI.Combinatorics.EditApproximation.Refinement.PhysicalWarmupQuery
import OAI.Combinatorics.EditApproximation.Geometry.DyadicQueryWindow
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A local warmup step gathers its candidate initial values and each
distinct wide child coordinate before evaluating the finite Bellman
minimum. Wide action enumeration makes no recursive oracle calls. -/

namespace EditApproximation



theorem localRefinementRepresentatives_congr_raw {n : ℕ} (N P F : ℕ) (a : ℚ)
    (left right : TargetInterval n → ℚ) (q : TargetInterval n) (hq : left q = right q)
    (heq : ∀ r ∈ rawRefinementCenters N P F a (left q) q, left r = right r) :
    localRefinementRepresentatives N P F a left q =
      localRefinementRepresentatives N P F a right q := by
  unfold localRefinementRepresentatives
  rw [← hq]
  apply List.flatMap_congr
  intro b hb
  congr 1
  apply List.filter_congr
  intro r hr
  rw [heq r (List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨b, hb, hr⟩))]



theorem wideWarmupInputs_action {nx ny M : ℕ} (parent : TargetInterval nx) (P : ℕ)
    (representatives : List (ℕ × TargetInterval ny))
    (action : RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M)
    (ha : action ∈ rationalActualWideActions parent representatives P) (i : Fin M) :
    action.childState i ∈ wideWarmupInputs parent P representatives := by
  obtain ⟨br, hbr, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨states, hs, rfl⟩ := List.mem_map.mp ha
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  refine ⟨br, hbr, List.mem_flatMap.mpr ?_⟩
  exact ⟨i, List.mem_finRange i, List.mem_map.mpr
    ⟨states i, finiteAssignments_sound M _ states hs i, rfl⟩⟩



theorem localWarmupStepQuery_value {ι : Type*} {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : ℚ) (initialRead : TargetInterval ny → FiniteQuery ι)
    (childRead : Fin M × TargetInterval ny → FiniteQuery ι) (oracle : ι → ℚ)
    (initial : TargetInterval ny → ℚ) (child : Fin M × TargetInterval ny → ℚ)
    (hinitial : ∀ r, (initialRead r).value oracle = initial r)
    (hchild : ∀ input, (childRead input).value oracle = child input) (q : TargetInterval ny) :
    (localWarmupStepQuery parent N P F a initialRead childRead q).value oracle =
      rationalBellman initial (fun q r => targetEndpointDistance q r) (128 * F)
        (rationalActualWideActions parent (localRefinementRepresentatives N P F a initial q) P) child q := by
  let centers := rawRefinementCenters N P F a (initial q) q
  let table := fun r => if r = q then initial q else finiteAnswerTable centers (centers.map initial) r
  have htable (r : TargetInterval ny) (hr : r ∈ centers) : table r = initial r := by
    dsimp only [table]
    split_ifs with heq
    · exact congrArg initial heq.symm
    · exact finiteAnswerTable_map centers initial r hr
  have htableq : table q = initial q := by simp only [table, ite_true]
  have hreps : localRefinementRepresentatives N P F a table q =
      localRefinementRepresentatives N P F a initial q :=
    localRefinementRepresentatives_congr_raw N P F a table initial q htableq
      (fun r hr => htable r (by simpa only [htableq] using hr))
  let representatives := localRefinementRepresentatives N P F a initial q
  let inputs := wideWarmupInputs (M := M) parent P representatives
  have hinputs : ∀ action ∈ rationalActualWideActions parent representatives P, ∀ i,
      finiteAnswerTable inputs (inputs.map child) (action.childState i) = child (action.childState i) := by
    intro action ha i
    exact finiteAnswerTable_map inputs child _ (wideWarmupInputs_action parent P representatives action ha i)
  simp only [localWarmupStepQuery, FiniteQuery.bind_value, hinitial, FiniteQuery.collect_value,
    hchild, FiniteQuery.value]
  change rationalBellman table _ _
    (rationalActualWideActions parent (localRefinementRepresentatives N P F a table q) P)
    (finiteAnswerTable
      (wideWarmupInputs parent P (localRefinementRepresentatives N P F a table q))
      ((wideWarmupInputs parent P (localRefinementRepresentatives N P F a table q)).map child)) q = _
  rw [hreps]
  unfold rationalBellman
  rw [htableq]
  congr 1
  apply List.map_congr_left
  intro action ha
  unfold rationalActionValue
  congr 1
  exact Finset.sum_congr rfl (fun i hi => hinputs action ha i)



theorem physicalWarmupStepQuery_value {ι α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (seedRead : PhysicalEntry M J target.length → FiniteQuery ι)
    (childRead : Fin M × TargetInterval target.length → FiniteQuery ι) (oracle : ι → ℚ)
    (U : PhysicalEntry M J target.length → ℕ)
    (hseed : ∀ state, (seedRead state).value oracle = (U state : ℚ))
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (t : ℕ) (q : TargetInterval target.length)
    (hchild : ∀ input, (childRead input).value oracle =
      physicalLocalWarmup source target U N P F A t (physicalChild node hbelow input.1, input.2)) :
    (physicalWarmupStepQuery source target N P F A seedRead childRead node q).value oracle =
      physicalLocalWarmup source target U N P F A (t + 1) (node, q) := by
  rw [physicalLocalWarmup]
  simp only [dite_eq_left hbelow, ite_eq_right hleaf]
  exact localWarmupStepQuery_value _ N P F (refinementFactor A F) _ _ oracle _ _
    (fun r => physicalInitialQuery_value source target N P F A seedRead oracle U hseed (node, r))
    hchild q

/-- Every child read of a positive warmup step carries its concrete
strict progress proof. The previous-pass seed reader is supplied by the
pass wrapper, so its own reads must carry the same strict proof. -/




theorem physicalWarmupRequestQuery_value {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (pass copy T S j : ℕ) (node : PhysicalNode M J) (q : TargetInterval target.length)
    (seedRead : PhysicalEntry M J target.length →
      FiniteQuery {child : PhysicalTableRequest M J target.length //
        child.combinedRank T S < (PhysicalTableRequest.warmup pass copy node j q).combinedRank T S})
    (values : PhysicalTableRequest M J target.length → ℚ)
    (U : PhysicalEntry M J target.length → ℕ)
    (hseed : ∀ state, (seedRead state).value (fun child => values child.val) = (U state : ℚ))
    (hchild : ∀ (hbelow : node.1.val < J) (input : Fin M × TargetInterval target.length),
      values (PhysicalTableRequest.warmup pass copy (physicalChild node hbelow input.1) (j - 1) input.2) =
        physicalLocalWarmup source target U N P F A (j - 1)
          (physicalChild node hbelow input.1, input.2)) :
    (physicalWarmupRequestQuery source target N P F A pass copy T S j node q seedRead).value
      (fun child => values child.val) = physicalLocalWarmup source target U N P F A j (node, q) := by
  cases j with
  | zero => exact physicalInitialQuery_value source target N P F A seedRead _ U hseed (node, q)
  | succ t =>
    dsimp only [physicalWarmupRequestQuery]
    split_ifs with hbelow hleaf
    · rw [physicalLocalWarmup]
      simp only [dite_eq_left hbelow, ite_eq_left hleaf]
      exact physicalInitialQuery_value source target N P F A seedRead _ U hseed (node, q)
    · apply physicalWarmupStepQuery_value source target N P F A seedRead _ _ U hseed
        node hbelow hleaf t q
      intro input
      exact hchild hbelow input
    · rw [physicalLocalWarmup]
      simp only [dite_eq_right hbelow]
      exact physicalInitialQuery_value source target N P F A seedRead _ U hseed (node, q)

end EditApproximation

end OAI
