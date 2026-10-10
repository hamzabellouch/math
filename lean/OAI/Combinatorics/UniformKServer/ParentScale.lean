import Mathlib
import OAI.Combinatorics.UniformKServer.CoarseData

namespace OAI

                                  
section

/-! Parent H is an actual persistent relative reference of the clipped sum
of persistent size trackers, not an oracle for the true size. -/
noncomputable section
namespace UniformKServer.ParentScale
open Finset RankData RankTracking CoarseData AllocationSchedule
open scoped Classical
variable {Ω R : Type*} [Fintype Ω] [Fintype R]

def trueX (I : R → Input Ω) (t : ℕ) (ω : Ω) : ℝ :=
  max (totalSize (fun r => (I r).posterior t ω)) cutoff

def estimateX (I : R → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  max (sizeEstimate I δ t ω) cutoff

def reference (I : R → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  held δ (fun s => estimateX I δ s ω) t

def lowerX (I : R → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  max cutoff (reference I δ t ω/(1+δ)^2)

theorem estimate_comparison (I : R → Input Ω) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) (ω : Ω) :
    compared δ (estimateX I δ t ω) (trueX I t ω) := by
  have hs := sizeEstimate_comparison I hδ t ω
  have hi : 1+δ ≠ 0 := ne_of_gt (by linarith)
  have hm := mul_le_mul_of_nonneg_left hs.1 (show 0 ≤ 1+δ by linarith)
  rw [←mul_assoc,mul_inv_cancel₀ hi,one_mul] at hm
  have hc : (cutoff:ℝ) ≤ (1+δ)*cutoff := by norm_num [cutoff] at *; linarith
  have hpos : 0 ≤ 1+δ := by linarith
  constructor
  · apply max_le
    · exact hm.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hpos)
    · exact hc.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hpos)
  · apply max_le
    · exact hs.2.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hpos)
    · exact hc.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hpos)

theorem reference_comparison (I : R → Input Ω) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) (ω : Ω) :
    trueX I t ω ≤ (1+δ)^2*reference I δ t ω ∧
      reference I δ t ω ≤ (1+δ)^2*trueX I t ω := by
  have hh := held_compared hδ.le (fun s =>
    le_trans (show (0:ℝ) ≤ cutoff by norm_num [cutoff]) (le_max_right (sizeEstimate I δ s ω) cutoff)) t
  have hx := estimate_comparison I hδ t ω
  have hpos : 0 ≤ 1+δ := by linarith
  constructor
  · have h := hx.1.trans (mul_le_mul_of_nonneg_left hh.1 hpos)
    change trueX I t ω ≤ (1+δ)*((1+δ)*reference I δ t ω) at h
    nlinarith only [h]
  · have h := hh.2.trans (mul_le_mul_of_nonneg_left hx.2 hpos)
    change reference I δ t ω ≤ (1+δ)*((1+δ)*trueX I t ω) at h
    nlinarith only [h]

theorem lower_bounds (I : R → Input Ω) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) (ω : Ω) :
    cutoff ≤ lowerX I δ t ω ∧ lowerX I δ t ω ≤ trueX I t ω ∧
      trueX I t ω ≤ (1+δ)^4*lowerX I δ t ω := by
  have h := reference_comparison I hδ t ω
  have hp : 0 < (1+δ)^2 := sq_pos_of_pos (by linarith)
  refine ⟨le_max_left _ _,?_,?_⟩
  · apply max_le (le_max_right _ _)
    apply (div_le_iff₀ hp).mpr
    change reference I δ t ω ≤ trueX I t ω*(1+δ)^2
    nlinarith only [h.2]
  · have hd : reference I δ t ω ≤ lowerX I δ t ω*(1+δ)^2 :=
      (div_le_iff₀ hp).mp (le_max_right cutoff _)
    have hm := mul_le_mul_of_nonneg_left hd hp.le
    nlinarith only [h.1,hm]

theorem true_positive (I : R → Input Ω) (t : ℕ) (ω : Ω) : 0 < trueX I t ω :=
  lt_of_lt_of_le (by norm_num [cutoff]) (le_max_right _ _)

theorem lower_positive (I : R → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) : 0 < lowerX I δ t ω :=
  lt_of_lt_of_le (by norm_num [cutoff]) (le_max_left _ _)

theorem estimate_change (I : R → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) :
    |estimateX I δ (t+1) ω-estimateX I δ t ω| ≤
      |sizeEstimate I δ (t+1) ω-sizeEstimate I δ t ω| := by
  unfold estimateX
  by_cases ha : cutoff ≤ sizeEstimate I δ (t+1) ω
  · rw [max_eq_left ha]
    by_cases hb : cutoff ≤ sizeEstimate I δ t ω
    · rw [max_eq_left hb]
    · rw [max_eq_right (le_of_not_ge hb),abs_of_nonneg (sub_nonneg.mpr ha),
        abs_of_nonneg (by linarith : 0 ≤ sizeEstimate I δ (t+1) ω-sizeEstimate I δ t ω)]
      linarith
  · rw [max_eq_right (le_of_not_ge ha)]
    by_cases hb : cutoff ≤ sizeEstimate I δ t ω
    · rw [max_eq_left hb,abs_of_nonpos (sub_nonpos.mpr hb),
        abs_of_nonpos (by linarith : sizeEstimate I δ (t+1) ω-sizeEstimate I δ t ω ≤ 0)]
      linarith
    · rw [max_eq_right (le_of_not_ge hb),sub_self,abs_zero]
      exact abs_nonneg _

theorem reference_charge (I : R → Input Ω) {δ K : ℝ} (hδ : 0 < δ)
    (hK : 1+2/δ ≤ K) (H : ℕ) (ω : Ω) :
    (∑ t ∈ range H, charge (reference I δ t ω) (reference I δ (t+1) ω)) ≤
      K*∑ t ∈ range H, |sizeEstimate I δ (t+1) ω-sizeEstimate I δ t ω| := by
  have hn (s : ℕ) : 0 ≤ estimateX I δ s ω :=
    le_trans (by norm_num [cutoff]) (le_max_right _ _)
  have hK0 : 0 ≤ K := by have := div_pos (by norm_num : (0:ℝ)<2) hδ; linarith
  exact (held_budget hδ hK hn H).trans (mul_le_mul_of_nonneg_left
    (sum_le_sum fun t _ => estimate_change I δ t ω) hK0)

end UniformKServer.ParentScale

end


end

end OAI
