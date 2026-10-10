import OAI.Combinatorics.EditApproximation.Geometry.CurrentQueryInputs

namespace OAI

/-! Shared group estimates depend only on the explicitly bounded sampled
input cover. Thus scanning or repeatedly scoring all cell members can
reuse gathered values rather than issue new recursive requests. -/

namespace EditApproximation

open Finset

theorem groupScaleEstimate_congr_queried {M Q b : ℕ} (h : ℚ)
    (envelope value value' : Fin M → ℚ)
    (draw : Fin (groupSampleCount M Q b h) → Fin M)
    (hvalue : ∀ i ∈ groupQueriedChildLabels M Q b h draw,
      envelope i = h → value i = value' i) :
    groupScaleEstimate (groupSampleCount M Q b h) h envelope value draw =
      groupScaleEstimate (groupSampleCount M Q b h) h envelope value' draw := by
  unfold groupScaleEstimate
  split_ifs with hexact
  · unfold groupScaleTrueCost
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · exact hvalue i (by simp only [groupQueriedChildLabels, hexact, ↓reduceIte, Finset.mem_univ]) hi
    · rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · apply hvalue _ _ hj
      simp only [groupQueriedChildLabels, hexact, ↓reduceIte]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · rfl

theorem dyadicUnskippedGroupEstimate_congr_cover {α : Type*}
    (source target : List α) {M b P exponent : ℕ}
    (parent : TargetInterval source.length) (tau a : ℚ) (F Q : ℕ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial value value' : Fin M → TargetInterval target.length → ℚ)
    (cell : ℕ × ℕ)
    (member : UnskippedBand source target parent b P exponent tau F child initial)
    (hb : 1 ≤ b)
    (hcenter : member.center ∈ cellRepresentativeStates target.length P F b a parentInitial
      ((2 : ℚ) ^ (-(exponent : ℤ))) cell)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (hvalue : ∀ scale : Fin (groupDyadicScales M b F).length,
      ∀ input ∈ groupCurrentInputCover source target parent b exponent Q cell
        (groupDyadicScaleAt M b F scale) (draw scale), value input.1 input.2 = value' input.1 input.2) :
    dyadicUnskippedGroupEstimate Q value member draw =
      dyadicUnskippedGroupEstimate Q value' member draw := by
  unfold dyadicUnskippedGroupEstimate unskippedGroupEstimate groupMemberEstimate
  congr 1
  apply Finset.sum_congr rfl
  intro scale _
  apply groupScaleEstimate_congr_queried
  intro i hi henvelope
  exact hvalue scale (i, member.rounded i)
    (actual_group_input_in_cover source target parent tau a F Q parentInitial child initial cell
      member hb hcenter _ (draw scale) i hi henvelope)

theorem rational_argmax_congr_on {ι : Type*} (members : List ι) (score score' : ι → ℚ)
    (hscore : ∀ member ∈ members, score member = score' member) :
    members.argmax score = members.argmax score' := by
  induction members with
  | nil => rfl
  | cons first rest ih =>
    rw [List.argmax_cons, List.argmax_cons, ih (fun member hm => hscore member (by simp [hm]))]
    cases hmax : rest.argmax score' with
    | none => rfl
    | some selected =>
      have hmem : selected ∈ rest := List.argmax_mem (by rw [hmax]; simp)
      dsimp only
      rw [hscore first (by simp), hscore selected (by simp [hmem])]

theorem selectGroupMember_congr_on {ι : Type*} (members : List ι) (hne : members ≠ [])
    (estimate estimate' : ι → ℚ)
    (heq : ∀ member ∈ members, estimate member = estimate' member) :
    selectGroupMember members hne estimate = selectGroupMember members hne estimate' := by
  unfold selectGroupMember
  rw [rational_argmax_congr_on members (fun member => -estimate member)
    (fun member => -estimate' member) (fun member hm => congrArg Neg.neg (heq member hm))]

theorem chooseCellGroupAction_congr_cover {α : Type*}
    (source target : List α) {M b P exponent : ℕ}
    (parent : TargetInterval source.length) (tau a : ℚ) (F Q : ℕ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial value value' : Fin M → TargetInterval target.length → ℚ)
    (cell : ℕ × ℕ) (hb : 1 ≤ b)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (hvalue : ∀ scale : Fin (groupDyadicScales M b F).length,
      ∀ input ∈ groupCurrentInputCover source target parent b exponent Q cell
        (groupDyadicScaleAt M b F scale) (draw scale), value input.1 input.2 = value' input.1 input.2) :
    chooseCellGroupAction source target parent b P F exponent Q tau a parentInitial child initial value cell draw =
      chooseCellGroupAction source target parent b P F exponent Q tau a parentInitial child initial value' cell draw := by
  let members := cellUnskippedBands source target parent b P F exponent tau a parentInitial child initial cell
  change (if hm : members = [] then none else some (chooseUnskippedGroup Q value members hm draw).rationalAction) =
    (if hm : members = [] then none else some (chooseUnskippedGroup Q value' members hm draw).rationalAction)
  split_ifs with hempty
  · rfl
  · have hselected : chooseUnskippedGroup Q value members hempty draw =
        chooseUnskippedGroup Q value' members hempty draw := by
      unfold chooseUnskippedGroup
      apply selectGroupMember_congr_on
      intro member hm
      apply dyadicUnskippedGroupEstimate_congr_cover source target parent tau a F Q parentInitial
        child initial value value' cell member hb _ draw hvalue
      exact (unskippedBandList_mem_iff _ _).mp hm
    exact congrArg (fun member => some member.rationalAction) hselected

end EditApproximation

end OAI
