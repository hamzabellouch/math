import OAI.Combinatorics.EditApproximation.Geometry.RoundedGroupStates
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Every actual unskipped rounded group input belongs to a common
small endpoint list determined by the cell, child and envelope label. -/

namespace EditApproximation



theorem groupRoundSpacing_pos (exponent : ℕ) (h : ℚ) : 0 < groupRoundSpacing exponent h := by
  apply Nat.ceil_pos.mpr
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem groupRoundSpacing_envelope_bound (exponent : ℕ) (h : ℚ) :
    h ≤ (2 : ℚ) ^ exponent * groupRoundSpacing exponent h := by
  have hpow : (0 : ℚ) < (2 : ℚ) ^ exponent := by positivity
  have hceil : (2 : ℚ) ^ (-(exponent : ℤ)) * h ≤ (groupRoundSpacing exponent h : ℚ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  have hmul := mul_le_mul_of_nonneg_left hceil hpow.le
  rw [zpow_neg, zpow_natCast] at hmul
  simpa only [← mul_assoc, mul_inv_cancel₀ hpow.ne', one_mul] using hmul

theorem bandRoundSpacing_group_spacing {ny M : ℕ} (exponent b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (initial : Fin M → TargetInterval ny → ℚ)
    (i : Fin M) (h : ℚ) (henvelope : bandChildEnvelope b band initial i = h) :
    bandRoundSpacing exponent b band initial i = groupRoundSpacing exponent h := by
  have heq := bandRoundSpacing_exact exponent b band initial i
  rw [henvelope] at heq
  have hceil := congrArg (fun r : ℚ => ⌈r⌉₊) heq
  simpa only [Nat.ceil_natCast, groupRoundSpacing] using hceil

theorem gridStateBox_sound {n g radius lo hi : ℕ} (hg : 0 < g) (r : TargetInterval n)
    (hr : r ∈ gridStateBox n g radius lo hi) :
    Nat.dist lo r.lo ≤ radius ∧ Nat.dist hi r.hi ≤ radius ∧ g ∣ r.lo ∧ g ∣ r.hi := by
  obtain ⟨s, hs, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨t, ht, hmake⟩ := List.mem_filterMap.mp hr
  have heq : r.lo = s ∧ r.hi = t := by
    unfold makeTargetState at hmake
    split_ifs at hmake with hvalid
    cases hmake
    exact ⟨rfl, rfl⟩
  rw [← heq.1] at hs
  rw [← heq.2] at ht
  have hlo := gridPointsBetween_sound hg hs
  have hhi := gridPointsBetween_sound hg ht
  refine ⟨?_, ?_, hlo.2.2, hhi.2.2⟩ <;> unfold Nat.dist <;> omega



theorem actual_rounded_group_input_mem {α : Type*} (source target : List α) {M b P exponent : ℕ}
    (parent : TargetInterval source.length) (tau a : ℚ) (F : ℕ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (member : UnskippedBand source target parent b P exponent tau F child initial)
    (hb : 1 ≤ b)
    (hcenter : member.center ∈ cellRepresentativeStates target.length P F b a parentInitial
      ((2 : ℚ) ^ (-(exponent : ℤ))) cell)
    (i : Fin M) (h : ℚ) (henvelope : member.envelope i = h) :
    member.rounded i ∈ groupRoundedStateList source target parent b exponent cell i h := by
  have hspacing := bandRoundSpacing_group_spacing exponent b member.actions initial i h henvelope
  have hgrid : groupRoundSpacing exponent h ∣ (member.rounded i).lo ∧
      groupRoundSpacing exponent h ∣ (member.rounded i).hi := by
    simpa only [UnskippedBand.rounded, canonicalRoundedBandAction, roundedBandAction, hspacing] using
      roundInterval_on_grid (bandRoundSpacing exponent b member.actions initial i)
        (member.actions.head member.nonempty i)
  have hwide : member.rounded i ∈ wideChildStateList parent member.center b P i :=
    finiteAssignments_sound M (wideChildStateList parent member.center b P) member.rounded member.wide_guard i
  have hwideFirst := (gridStateBox_sound (by unfold seedGridSpacing; omega) (member.rounded i) hwide).1
  have htheta : 0 ≤ (2 : ℚ) ^ (-(exponent : ℤ)) ∧ (2 : ℚ) ^ (-(exponent : ℤ)) ≤ 1 := by
    refine ⟨(zpow_pos (by norm_num : (0 : ℚ) < 2) _).le, ?_⟩
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2))
  have hfirst := wide_firstEndpoint_near_cell cell (by unfold seedGridSpacing; omega) htheta hb
    member.center (member.rounded i) ((sourceChild parent i).lo - parent.lo)
    (List.mem_filter.mp hcenter).1 hwideFirst
  have hgap := member.imbalance_guard i
  change |rationalStateGap _ _ (member.rounded i)| ≤ 2 * member.envelope i at hgap
  rw [henvelope] at hgap
  unfold rationalStateGap at hgap
  have hgapDistance := lengthGap_guard_distance (member.rounded i)
    (substring source (sourceChild parent i).lo (sourceChild parent i).hi).length h hgap
  unfold groupRoundedStateList
  apply gridGapStates_complete (groupRoundSpacing_pos exponent h) _ _ hgapDistance hgrid
  simpa only [mul_assoc] using hfirst

theorem groupRoundedStateList_length {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b exponent : ℕ) (cell : ℕ × ℕ)
    (i : Fin M) (h : ℚ) (hh : 0 < h) :
    ((groupRoundedStateList source target parent b exponent cell i h).length : ℚ) ≤
      208 * ((2 : ℚ) ^ exponent) ^ 2 * (1 + b / h) := by
  exact gridGapStates_rounded_count _ _ _ _ b h ((2 : ℚ) ^ exponent)
    (groupRoundSpacing_pos exponent h) hh (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2))
    (groupRoundSpacing_envelope_bound exponent h)

end EditApproximation

end OAI
