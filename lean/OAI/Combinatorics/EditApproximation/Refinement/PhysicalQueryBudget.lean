import OAI.Combinatorics.EditApproximation.Geometry.DyadicQueryWindow
import OAI.Combinatorics.EditApproximation.Geometry.SeedFactorSchedule

namespace OAI

/-! The literal online loop is bounded by the applicable scale window,
which is polynomial in ell throughout the computed factor schedule. -/

namespace EditApproximation

open Finset

theorem refinement_query_window_length (N F initialExponent : ℕ) (A w : ℚ)
    (hF : 1 ≤ F) (hFbound : (F : ℚ) ≤ (2 : ℚ) ^ initialExponent)
    (hAbound : A ≤ (2 : ℚ) ^ initialExponent) :
    (dyadicQueryWindow N w (refinementFactor A F) F).length ≤ initialExponent + 8 := by
  have hFpos : (0 : ℚ) < F := by exact_mod_cast (by omega : 0 < F)
  have hfactor : refinementFactor A F ≤ (2 : ℚ) ^ initialExponent / F := by
    apply max_le
    · exact (le_div_iff₀ hFpos).2 (by simpa only [one_mul] using hFbound)
    · exact div_le_div_of_nonneg_right hAbound hFpos.le
  have hproduct := mul_le_mul_of_nonneg_right hfactor hFpos.le
  rw [div_mul_cancel₀ _ hFpos.ne'] at hproduct
  have hbudget : 128 * refinementFactor A F * F ≤ (2 : ℚ) ^ (initialExponent + 7) := by
    have h := mul_le_mul_of_nonneg_left hproduct (by norm_num : (0 : ℚ) ≤ 128)
    rw [pow_add]
    norm_num only [show (2 : ℚ) ^ 7 = 128 by norm_num]
    nlinarith only [h]
  simpa only [Nat.add_assoc, show (7 : ℕ) + 1 = 8 by rfl] using
    dyadicQueryWindow_length_le N (initialExponent + 7) w (refinementFactor A F) F
      (le_max_left _ _) (by exact_mod_cast hF) hbudget

section PhysicalQuery

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ)

local notation "representatives" => stageRepresentatives source target U N P F A

theorem physicalProgramOnline_query_indices_window (node : PhysicalNode M J)
    (q : TargetInterval target.length) :
    ((List.finRange (representatives node).length).filter fun representative => decide
      (physicalProgramOnlineGuard source target U N P F A node q
        ((representatives node).get representative))).length ≤
      (dyadicQueryWindow N (stageInitial source target U N P F A (node, q)) (refinementFactor A F) F).length := by
  let indices := (List.finRange (representatives node).length).filter fun representative => decide
    (physicalProgramOnlineGuard source target U N P F A node q ((representatives node).get representative))
  let scales := indices.map fun representative => ((representatives node).get representative).1
  have hrep : (representatives node).Nodup := representativeList_nodup N P F _ _
  have hscales : scales.Nodup := by
    apply ((List.nodup_finRange _).filter _).map_on
    intro i hi j hj hscale
    have hqi := of_decide_eq_true (List.mem_filter.mp hi).2
    have hqj := of_decide_eq_true (List.mem_filter.mp hj).2
    have hcenter : ((representatives node).get i).2 = ((representatives node).get j).2 :=
      hqi.1.trans ((congrArg (fun b => roundInterval (seedGridSpacing b P) q) hscale).trans hqj.1.symm)
    exact hrep.injective_get (Prod.ext hscale hcenter)
  have hsub : scales.toFinset ⊆
      (dyadicQueryWindow N (stageInitial source target U N P F A (node, q)) (refinementFactor A F) F).toFinset := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
    have hguard := of_decide_eq_true (List.mem_filter.mp hi).2
    apply List.mem_toFinset.mpr
    exact List.mem_filter.mpr ⟨representativeList_scale_mem _ _ (List.get_mem (representatives node) i),
      decide_eq_true hguard.2⟩
  have hcard := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  simpa only [List.toFinset_card_of_nodup hscales, scales, List.length_map] using hcard

theorem physicalProgramOnline_length_window (T exponent H : ℕ) (tau η κ : ℚ)
    {R : ℕ} [NeZero R]
    (stream : PhysicalOnlineStreams source target U N P F A T exponent H tau R)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length) (t : ℕ)
    (q : TargetInterval target.length) :
    (physicalProgramOnline source target U N P F A T exponent H tau η κ stream node children t q).length ≤
      (dyadicQueryWindow N (stageInitial source target U N P F A (node, q)) (refinementFactor A F) F).length := by
  unfold physicalProgramOnline
  split_ifs with hbelow
  · exact (List.length_filterMap_le _ _).trans
      (physicalProgramOnline_query_indices_window source target U N P F A node q)
  · exact Nat.zero_le _

end PhysicalQuery

end EditApproximation

end OAI
