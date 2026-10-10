import OAI.Combinatorics.EditApproximation.Refinement.PhysicalGlobalQuery
import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoSimulation

namespace OAI

/-! The global query body computes the local pass recurrence on every seed and draw. -/

namespace EditApproximation

section Value

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

theorem physicalGlobalQuery_warmup (pass copy : ℕ) (node : PhysicalNode M J)
    (j : ℕ) (hj : j ≤ T) (q : TargetInterval target.length) :
    physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node j q) =
    physicalWarmupRequestQuery source target N P F (factor pass) pass copy T S j node q
      (globalSeedRead N T S copies multiplier initial (PhysicalTableRequest.warmup pass copy node j q)) := by
  unfold physicalGlobalQuery
  dsimp only
  erw [dite_eq_left (show (PhysicalTableRequest.warmup pass copy node j q).index ≤ T from hj)]
  rfl

theorem physicalGlobalQuery_refinement_value (request : PhysicalTableRequest M J target.length)
    (hindex : T < request.index) (hbelow : request.node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length request.node).hi -
      (physicalSourceInterval source.length request.node).lo ≤ 1)
    (values : PhysicalTableRequest M J target.length → ℚ) :
    (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request).value (fun child => values child.val) =
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt hindex) request.node hbelow
      (group request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      (integer request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      request.state).value (fun child => values child.val) := by
  unfold physicalGlobalQuery
  dsimp only
  erw [dite_eq_right (Nat.not_le.mpr hindex), dite_eq_left hbelow, dite_eq_right hshort]
  rw [FiniteQuery.mapKeys_value]
  rfl


theorem globalSeedRead_value (parent : PhysicalTableRequest M J target.length)
    (q : TargetInterval target.length) :
    (globalSeedRead N T S copies multiplier initial parent (parent.node, q)).value
      (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial child.val) =
    (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial parent.pass (parent.node, q) : ℚ) := by
  by_cases hp : parent.pass = 0
  · rw [globalSeedRead, ite_eq_left rfl, dite_eq_left hp]
    change (initial (parent.node, q) : ℚ) = _
    rw [hp]
    rfl
  · simp only [globalSeedRead, ite_true, dite_eq_right hp]
    rw [physicalMedianSeedQuery_value]
    have hprev (copy : Fin copies) :
        previousPassRequest T S copy.val parent q =
          PhysicalTableRequest.refinement (parent.pass - 1) copy.val parent.node T S q := rfl
    simp only [hprev, localRequestValue_refinement]
    obtain ⟨pass, hpass⟩ := Nat.exists_eq_succ_of_ne_zero hp
    simp only [hpass, Nat.succ_eq_add_one, Nat.add_sub_cancel, localSeedSequence]

theorem localRequestValue_initial (pass copy : ℕ) (node : PhysicalNode M J)
    (q : TargetInterval target.length) :
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node 0 q) =
    stageInitial source target
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass) N P F (factor pass) (node, q) := by
  rw [localRequestValue_warmup source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta group integer initial pass copy node 0 (Nat.zero_le T)]
  rfl

theorem localRequestValue_mass (pass copy : ℕ) (node : PhysicalNode M J)
    (q : TargetInterval target.length) :
    (∑ j : Fin T, localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node j.val q)) / T =
    physicalLocalWarmupMass source target
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass) N P F (factor pass) T (node, q) := by
  unfold physicalLocalWarmupMass
  rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => localRequestValue_warmup source target N P F exponent H Q
    T S copies factor multiplier tau eta kappa delta group integer initial pass copy node j.val
      (Nat.le_of_lt j.isLt) q)


theorem localPassValue_step (seed : PhysicalEntry M J target.length → ℕ)
    (pass copy : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (t : ℕ) (ht : 0 < t) (q : TargetInterval target.length) :
    let children := fun i s r => localPassValue source target N P F exponent H Q T factor
      tau eta kappa delta group integer seed pass copy (physicalChild node hbelow i) s r
    localPassValue source target N P F exponent H Q T factor tau eta kappa delta group integer
      seed pass copy node t q =
    rationalLocalWideStep source target (physicalSourceInterval source.length node)
      N P F exponent Q tau (refinementFactor (factor pass) F) delta
      (fun r => stageInitial source target seed N P F (factor pass) (node, r))
      (physicalLocalChildMass source target seed N P F (factor pass) T node hbelow)
      (fun i r => stageInitial source target seed N P F (factor pass) (physicalChild node hbelow i, r))
      (fun i r => children i (t - 1) r) (fun i r => children i t r)
      (group pass copy ⟨node, hbelow⟩ (Fin.ofNat R (t - 1)))
      (localOnlineCandidates source target (physicalSourceInterval source.length node)
        N P F exponent H tau (refinementFactor (factor pass) F) eta kappa
        (fun r => stageInitial source target seed N P F (factor pass) (node, r))
        (physicalLocalChildMass source target seed N P F (factor pass) T node hbelow)
        (fun i r => stageInitial source target seed N P F (factor pass) (physicalChild node hbelow i, r))
        children (t - 1) (integer pass copy ⟨node, hbelow⟩ (Fin.ofNat R (t - 1))) q) q := by
  dsimp only
  cases t with
  | zero => omega
  | succ t =>
    unfold localPassValue
    rw [physicalLocalRefinement]
    simp only [dite_eq_left hbelow, ite_eq_right hshort, Nat.add_sub_cancel,
      physicalLocalOnline]
    rfl

theorem physicalRefinementDataRequestQuery_localValue (pass copy : ℕ) (node : PhysicalNode M J)
    (hbelow : node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (t : ℕ) (ht : 0 < t) (q : TargetInterval target.length) :
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor pass) F) eta kappa delta pass copy T S t ht node hbelow
      (group pass copy ⟨node, hbelow⟩ (Fin.ofNat R (t - 1)))
      (integer pass copy ⟨node, hbelow⟩ (Fin.ofNat R (t - 1))) q).value
        (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial child.val) =
    localPassValue source target N P F exponent H Q T factor tau eta kappa delta group integer
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass) pass copy node t q := by
  rw [physicalRefinementDataRequestQuery_value]
  dsimp only
  simp_rw [localRequestValue_initial source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta group integer initial,
    localRequestValue_mass source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial,
    localRequestValue_refinement source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial]
  exact (localPassValue_step source target N P F exponent H Q T factor tau eta kappa delta
    group integer _ pass copy node hbelow hshort t ht q).symm


theorem physicalGlobalQuery_value (request : PhysicalTableRequest M J target.length) :
    (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request).value
        (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial child.val) =
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request := by
  rcases request with ⟨pass, copy, node, index, q⟩
  by_cases hj : index ≤ T
  · change (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node index q)).value _ = _
    rw [physicalGlobalQuery_warmup source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy node index hj q]
    change _ = localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node index q)
    rw [localRequestValue_warmup source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy node index hj q]
    apply physicalWarmupRequestQuery_value_local
    · intro r
      exact globalSeedRead_value source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial _ r
    · intro hbelow input
      exact localRequestValue_warmup source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass copy (physicalChild node hbelow input.1)
        (index - 1) (by omega) input.2
  · obtain ⟨t, hi⟩ : ∃ t, index = T + t := ⟨index - T, by omega⟩
    subst index
    have ht : 0 < t := by omega
    change (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial (PhysicalTableRequest.refinement pass copy node T t q)).value _ =
      localRequestValue source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial (PhysicalTableRequest.refinement pass copy node T t q)
    rw [localRequestValue_refinement source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy node t q]
    by_cases hbelow : node.1.val < J
    · by_cases hshort : (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1
      · have hterminal : localPassValue source target N P F exponent H Q T factor tau eta kappa delta
            group integer (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
              tau eta kappa delta group integer initial pass) pass copy node t q =
            stageInitial source target
              (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
                tau eta kappa delta group integer initial pass) N P F (factor pass) (node, q) := by
          unfold localPassValue
          rw [physicalLocalRefinement, dite_eq_left hbelow, ite_eq_left hshort]
        rw [hterminal]
        unfold physicalGlobalQuery
        dsimp only
        erw [dite_eq_right (show ¬ (PhysicalTableRequest.refinement pass copy node T t q).index ≤ T
          from hj), dite_eq_left hbelow, dite_eq_left hshort]
        apply physicalInitialQuery_value_local
        intro r
        exact globalSeedRead_value source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial _ r
      · erw [physicalGlobalQuery_refinement_value source target N P F exponent H Q T S copies
          factor multiplier tau eta kappa delta group integer initial
          (PhysicalTableRequest.refinement pass copy node T t q) (by change T < T + t; omega)
          hbelow hshort]
        refine (physicalRefinementDataRequestQuery_localValue source target N P F exponent H Q T S copies
          factor multiplier tau eta kappa delta group integer initial pass copy node hbelow hshort
          (T + t - T) (by omega) q).trans ?_
        rw [Nat.add_sub_cancel_left]
    · have hterminal : localPassValue source target N P F exponent H Q T factor tau eta kappa delta
          group integer (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
            tau eta kappa delta group integer initial pass) pass copy node t q =
          stageInitial source target
            (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
              tau eta kappa delta group integer initial pass) N P F (factor pass) (node, q) := by
        unfold localPassValue
        rw [physicalLocalRefinement, dite_eq_right hbelow]
      rw [hterminal]
      unfold physicalGlobalQuery
      dsimp only
      erw [dite_eq_right (show ¬ (PhysicalTableRequest.refinement pass copy node T t q).index ≤ T
        from hj), dite_eq_right hbelow]
      apply physicalInitialQuery_value_local
      intro r
      exact globalSeedRead_value source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial _ r

theorem physicalGlobalProgramValue (request : PhysicalTableRequest M J target.length) :
    rankedProgramValue (PhysicalTableRequest.combinedRank T S)
      (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial) request =
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request :=
  rankedProgramValue_eq _ _ _
    (physicalGlobalQuery_value source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial) request


end Value

end EditApproximation

end OAI
