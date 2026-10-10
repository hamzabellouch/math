import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSelectionProgram

namespace OAI

/-! The literal query-filtered online loop has at most one candidate per scale. -/

namespace EditApproximation

open Finset

theorem makeTargetState_endpoints {n lo hi : ℕ} {q : TargetInterval n}
    (h : makeTargetState n lo hi = some q) : q.lo = lo ∧ q.hi = hi := by
  unfold makeTargetState at h
  split_ifs at h with hv
  · cases h
    exact ⟨rfl, rfl⟩

theorem targetStates_nodup (n : ℕ) : (targetStates n).Nodup := by
  unfold targetStates
  apply List.nodup_flatMap.mpr
  constructor
  · intro lo _
    apply (List.nodup_range (n := n + 1)).filterMap
    intro hi hi' q hq hq'
    have h := (makeTargetState_endpoints (Option.mem_def.mp hq)).2
    have h' := (makeTargetState_endpoints (Option.mem_def.mp hq')).2
    exact h.symm.trans h'
  · apply (List.nodup_range (n := n + 1)).imp
    intro lo lo' hne q hq hq'
    obtain ⟨hi, _, hq⟩ := List.mem_filterMap.mp hq
    obtain ⟨hi', _, hq'⟩ := List.mem_filterMap.mp hq'
    exact hne ((makeTargetState_endpoints hq).1.symm.trans (makeTargetState_endpoints hq').1)

theorem dyadicScales_nodup (N : ℕ) : (dyadicScales N).Nodup :=
  (List.nodup_range (n := Nat.log 2 N + 1)).map (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)))

theorem representativeList_nodup {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) : (representativeList N P F a initial).Nodup := by
  unfold representativeList
  apply List.nodup_flatMap.mpr
  constructor
  · intro b _
    exact ((targetStates_nodup n).filter _).map (fun _ _ heq => congrArg Prod.snd heq)
  · apply (dyadicScales_nodup N).imp
    intro b b' hne pair hp hp'
    obtain ⟨r, _, heq⟩ := List.mem_map.mp hp
    obtain ⟨r', _, heq'⟩ := List.mem_map.mp hp'
    exact hne ((congrArg Prod.fst heq).trans (congrArg Prod.fst heq').symm)

theorem representativeList_scale_mem {n N P F : ℕ} (a : ℚ)
    (initial : TargetInterval n → ℚ) {br : ℕ × TargetInterval n}
    (hbr : br ∈ representativeList N P F a initial) : br.1 ∈ dyadicScales N := by
  obtain ⟨b, hb, hbr⟩ := List.mem_flatMap.mp hbr
  obtain ⟨r, _, heq⟩ := List.mem_map.mp hbr
  exact (congrArg Prod.fst heq) ▸ hb

section Online

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H : ℕ) (tau η κ : ℚ)

local notation "representatives" => stageRepresentatives source target U N P F A

/-- A fixed query retains at most one original representative index for
each scale. This is a pathwise statement on every initial seed. -/
theorem physicalProgramOnline_query_indices_length (node : PhysicalNode M J)
    (q : TargetInterval target.length) :
    ((List.finRange (representatives node).length).filter fun representative => decide
      (physicalProgramOnlineGuard source target U N P F A node q
        ((representatives node).get representative))).length ≤ (dyadicScales N).length := by
  let indices := (List.finRange (representatives node).length).filter fun representative => decide
    (physicalProgramOnlineGuard source target U N P F A node q ((representatives node).get representative))
  let scales := indices.map fun representative => ((representatives node).get representative).1
  have hrep : (representatives node).Nodup := representativeList_nodup N P F _ _
  have hscales : scales.Nodup := by
    apply ((List.nodup_finRange _).filter _).map_on
    intro i hi j hj hscale
    have hqi := of_decide_eq_true (List.mem_filter.mp hi).2
    have hqj := of_decide_eq_true (List.mem_filter.mp hj).2
    have hcenter : ((representatives node).get i).2 = ((representatives node).get j).2 := by
      exact hqi.1.trans ((congrArg (fun b => roundInterval (seedGridSpacing b P) q) hscale).trans hqj.1.symm)
    exact hrep.injective_get (Prod.ext hscale hcenter)
  have hsub : scales.toFinset ⊆ (dyadicScales N).toFinset := by
    intro b hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
    exact List.mem_toFinset.mpr (representativeList_scale_mem _ _ (List.get_mem (representatives node) i))
  have hcard := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  simpa only [List.toFinset_card_of_nodup hscales, scales, List.length_map] using hcard

/-- The actual online action loop produces at most one action per dyadic
scale, including failed band tests and every initial seed. -/
theorem physicalProgramOnline_length {R : ℕ} [NeZero R]
    (stream : PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length) (t : ℕ)
    (q : TargetInterval target.length) :
    (physicalProgramOnline source target U N P F A T thetaExponent H tau η κ stream node children t q).length ≤
      (dyadicScales N).length := by
  unfold physicalProgramOnline
  split_ifs with hbelow
  · exact (List.length_filterMap_le _ _).trans
      (physicalProgramOnline_query_indices_length source target U N P F A node q)
  · exact Nat.zero_le _

end Online

end EditApproximation

end OAI
