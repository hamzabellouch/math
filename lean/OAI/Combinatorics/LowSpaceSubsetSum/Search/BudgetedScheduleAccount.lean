import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedSchedule
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSnapshots
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationProgram

namespace OAI

/-! # All-outcome work bounds for the concrete residue schedule -/

namespace LowSpaceSubsetSum.BudgetedSchedule

open BudgetedSeparatorFlow

variable {n g : ℕ}

theorem account (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (blocks : List (StoredSeparatorCheck.Block n g)) (budget : ℕ)
    (signedTarget : ℤ) (hn : 10000 ≤ n)
    (hraw : ∀ side i, (D.leaves side i).occurrences.card ≤ D.capacity)
    (hC : D.capacity ≤ 2 ^ n)
    (hcopy : ∀ z side (P : StoredRestriction n), (12 * n + 32) *
      2 ^ (Nat.clog 2 ({D.parentData side z with maskRestriction := P.semantic}.pair 1).leftArray.size + 1) ≤ B) :
    Account budget (run D F hF B blocks signedTarget budget) := by
  apply BudgetedResidueLoop.account
  intro z b
  exact BudgetedBucket.account (D.bucket z) F F hF hF B _
    (fun a c k => BudgetedSeparatorArrays.account (2 ^ n) signedTarget blocks a c k)
    hn (fun j => hraw 0 ⟨2 * j.val, by omega⟩)
    (fun j => hraw 0 ⟨2 * j.val + 1, by omega⟩)
    (fun j => hraw 1 ⟨2 * j.val, by omega⟩)
    (fun j => hraw 1 ⟨2 * j.val + 1, by omega⟩)
    hC hC (hcopy z 0 StoredRestriction.empty) (hcopy z 1) b

end LowSpaceSubsetSum.BudgetedSchedule

namespace LowSpaceSubsetSum.RepresentationData

variable {n : ℕ} (D : RepresentationData n)

theorem zeroSetup_inputScale_le : inputScale D.zeroSetup.input ≤ inputScale D.input := by
  simp only [zeroSetup, inputScale, inputBits, inputMaximum, zero_max]
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (max_le_max le_rfl (Nat.clog_mono_right 2
      (Nat.add_le_add_left (le_max_right _ _) 1))) n) 2

/-- The capacity checks follow from the input guard on every history, not
from a successful representation or a favorable resource event. -/
theorem schedule_account (h : D.zeroSetup.PrimeHistory) (r : D.zeroSetup.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale D.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (q : ℕ) (hq : 0 < q) (F : IndexedMask n) (hF : F.semantic = h.1.1.1.2)
    (blocks : List (StoredSeparatorCheck.Block n (2 * RepresentationSetup.blockHalf n 0)))
    (budget : ℕ) :
    BudgetedSeparatorFlow.Account budget
      (BudgetedSchedule.run (D.scheduleData h r hn hlog q hq) F hF
        (representationBufferCapacity n) blocks
        (D.scheduleData h r hn hlog q hq).target budget) := by
  have hzscale : Real.logb 2 (inputScale D.zeroSetup.input : ℝ) ≤ (n : ℝ) / 1000000000 := by
    apply (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) ?_ ?_).trans hscale
    · exact_mod_cast (show 0 < inputScale D.zeroSetup.input by unfold inputScale; omega)
    · exact_mod_cast D.zeroSetup_inputScale_le
  apply BudgetedSchedule.account _ F hF (representationBufferCapacity n) blocks budget _ hn
  · intro side i
    have hr := D.zeroSetup.rawLeaf_main_card h.1.1.1 h.1.1.2 h.1.2 hn hlog hzscale side i
    exact_mod_cast hr.trans (RepresentationSetup.main_leaf_rate_le_capacity hn)
  · change 2 ^ (199 * n / 1000) ≤ 2 ^ n
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · intro z side P
    let E := ({(D.zeroSetup.scheduleData h r hn hlog q hq).parentData side z with
      maskRestriction := P.semantic}).pair 1
    have hs := D.zeroSetup.schedule_snapshotCells_le_buffer h r hn hlog hzscale
      q hq z side P.semantic 1 E.start
    simpa only [RepresentationPairData.snapshotCells, Tournament.nodes_exact,
      RepresentationPairData.leftArray, RepresentationParentData.pair,
      RepresentationScheduleData.parentData, RepresentationScheduleData.leaves,
      RepresentationSetup.scheduleData, scheduleData] using hs

end LowSpaceSubsetSum.RepresentationData

end OAI
