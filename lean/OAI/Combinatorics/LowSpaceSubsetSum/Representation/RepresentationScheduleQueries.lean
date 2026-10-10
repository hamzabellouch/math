import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScheduleMatching

namespace OAI

/-! # Concrete child-stream and reader-query budgets for the full schedule -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

namespace RepresentationParentData

variable {n : ℕ} (D : RepresentationParentData n)

theorem pair_outputUniverse_empty (j : Fin 2) :
    ({ D with maskRestriction := MaskRestriction.empty }.pair j).outputUniverse =
      (RepresentationUniverse.children D.leaves j).filter (fun x =>
        RepresentationUniverse.childWeight D.weights x % D.lowModulus =
          D.childResidues j % D.lowModulus) := by
  classical
  let E : RepresentationParentData n := { D with maskRestriction := MaskRestriction.empty }
  change (E.pair j).outputUniverse = _
  ext x
  rw [← (E.pair j).output_toFinset]
  simp only [List.mem_toFinset, RepresentationPairData.output_mem,
    RepresentationUniverse.children, Finset.mem_filter, Finset.mem_product]
  simp only [E, pair, weights, MaskRestriction.accept_eq_true, MaskRestriction.empty_compatible,
    and_true, and_assoc]

end RepresentationParentData

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)
variable (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
variable (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
variable (q : ℕ) (hq : 0 < q)

/-- Exact identification with the four raw child counts used in the resource
event, including both complementary residues. -/
theorem schedule_unrestrictedChildCount :
    ((R.scheduleData h r hn hlog q hq).parentData 0 0).unrestrictedChildCount +
      ((R.scheduleData h r hn hlog q hq).parentData 1 0).unrestrictedChildCount =
        RepresentationMoments.G (prefixModulus_pos h.2 1) (prefixModulus_pos h.2 2)
          (R.signedWeights h.1.1.1)
          (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2
            (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) 0)
          (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2
            (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) 1)
          (R.signedTarget h.1.1.1) r := by
  classical
  unfold RepresentationParentData.unrestrictedChildCount RepresentationMoments.G
  rw [RepresentationParentData.pair_outputUniverse_empty,
    RepresentationParentData.pair_outputUniverse_empty,
    RepresentationParentData.pair_outputUniverse_empty,
    RepresentationParentData.pair_outputUniverse_empty]
  simp only [add_assoc]
  repeat' apply congrArg₂ Nat.add
  all_goals
    apply congrArg Finset.card
    ext x
    simp only [residueFiltered, Finset.mem_filter, normalizedResidue_eq_iff,
      ResidueMatchAccounting.complement_val]
  · have hr : (r.2.1.val : ℤ) % (prefixModulus h.2.val 1 : ℤ) = r.2.1.val :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.2.1.isLt)
    change (_ ∧ _ = (r.2.1.val : ℤ) % (prefixModulus h.2.val 1 : ℤ)) ↔ (_ ∧ _ = _)
    rw [hr]
    rfl
  · rfl
  · have hr : (r.2.2.val : ℤ) % (prefixModulus h.2.val 2 : ℤ) = r.2.2.val :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.2.2.isLt)
    change (_ ∧ _ = (r.2.2.val : ℤ) % (prefixModulus h.2.val 2 : ℤ)) ↔ (_ ∧ _ = _)
    rw [hr]
    rfl
  · rfl

theorem schedule_child_resource (hlarge : 20000 ≤ n)
    (hgood : R.AllocatedResourceGood hlarge hlog ⟨h, r⟩) :
    (((R.scheduleData h r hn hlog q hq).parentData 0 0).unrestrictedChildCount +
      ((R.scheduleData h r hn hlog q hq).parentData 1 0).unrestrictedChildCount : ℝ) ≤
        (inputScale R.input : ℝ) ^ 200 * (2 : ℝ) ^ R.resourceGamma h.1.1.1 := by
  rw [← Nat.cast_add, R.schedule_unrestrictedChildCount h r hn hlog q hq]
  exact hgood.1

theorem schedule_matching_resource (hlarge : 20000 ≤ n)
    (hgood : R.AllocatedResourceGood hlarge hlog ⟨h, r⟩) :
    ((((R.scheduleData h r hn hlog q hq).lowMatchingUniverse 0).card +
      ((R.scheduleData h r hn hlog q hq).lowMatchingUniverse 1).card : ℕ) : ℝ) ≤
        (inputScale R.input : ℝ) ^ 200 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  rw [R.schedule_lowMatchingUniverse_card h r hn hlog q hq,
    R.schedule_lowMatchingUniverse_card h r hn hlog q hq]
  exact hgood.2.1

/-- Reader queries over all prefixes in a side of the full residue loop. -/
theorem schedule_queryVisits_sum_bound (B : ℕ) (side : Fin 2) :
    ∑ z : Fin q, ((R.scheduleData h r hn hlog q hq).parentData side z.val).queryVisits B
      (R.scheduleData h r hn hlog q hq).topOrder MaskRestriction.empty ≤
      (6 * ((R.scheduleData h r hn hlog q hq).parentData side 0).unrestrictedChildCount + 2) *
        (∑ z : Fin q, ((R.scheduleData h r hn hlog q hq).parentData side z.val).taskStarts B
          (R.scheduleData h r hn hlog q hq).topOrder MaskRestriction.empty) +
        (mixerSize n + 1) * ((R.scheduleData h r hn hlog q hq).lowMatchingUniverse side).card := by
  let D := R.scheduleData h r hn hlog q hq
  have hs := Finset.sum_le_sum (fun (z : Fin q) (_ : z ∈ Finset.univ) =>
    (D.parentData side z.val).queryVisits_le_tasks_matching B D.topOrder MaskRestriction.empty)
  simp only [D.unrestrictedChildCount_eq_zero, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hs
  exact hs.trans (Nat.add_le_add_left
    (R.schedule_matchingVisits_sum_bound h r hn hlog q hq B side) _)

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
