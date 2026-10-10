import Mathlib
import OAI.Combinatorics.UniformKServer.EpochAlphaCharge
import OAI.Combinatorics.UniformKServer.StarSchedules

namespace OAI

                                 
section

/-! Uniform-in-law coarse charges of the actual input. In particular a parent
refresh pays for the entire old and new star without a factor of ell. -/
noncomputable section
namespace UniformKServer.StarBudget
open Finset StarRanks StarSchedules RankTracking CoarseData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem total_held_parent (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    (∑ i, held d t ω i) ≤ (11/10)*ParentScale.trueX (parentInput d) t ω := by
  calc
    _ ≤ (11/10)*(∑ i, RankData.totalSize (fun j => (input d i j).posterior t ω)) := by
      rw [mul_sum]
      exact sum_le_sum fun i _ => CoarseBridge.held_bound _ _ _
    _ ≤ (11/10)*RankData.totalSize (fun j => (parentInput d j).posterior t ω) :=
      mul_le_mul_of_nonneg_left (size_sum d t ω) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)

theorem total_held_reference (d : Data Ω ι k) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (t : ℕ) (ω : Ω) : (∑ i, held d t ω i) ≤ 5*ParentScale.reference (parentInput d) δ t ω := by
  have hx := ParentScale.reference_comparison (parentInput d) hδ t ω
  have hr : 0 ≤ ParentScale.reference (parentInput d) δ t ω := by
    have hp := ParentScale.true_positive (parentInput d) t ω
    have hf : 0 < (1+δ)^2 := sq_pos_of_pos (by linarith)
    exact le_of_lt (pos_of_mul_pos_right (lt_of_lt_of_le hp hx.1) hf.le)
  have hf : (1+δ)^2 ≤ (4:ℝ) := by nlinarith [sq_nonneg δ]
  have hm := mul_le_mul_of_nonneg_right hf hr
  linarith [total_held_parent d t ω,hx.1]

theorem parent_step (d : Data Ω ι k) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (t : ℕ) (ω : Ω) :
    (if parentRefresh d δ t ω then EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) ≤
      5*AllocationSchedule.charge (ParentScale.reference (parentInput d) δ t ω)
        (ParentScale.reference (parentInput d) δ (t+1) ω) := by
  unfold parentRefresh AllocationSchedule.charge
  by_cases he : ParentScale.reference (parentInput d) δ t ω=ParentScale.reference (parentInput d) δ (t+1) ω
  · simp only [he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,↓reduceIte,mul_zero,le_refl]
  · simp only [ne_eq,decide_eq_true_eq,Ne.symm he,he,↓reduceIte]
    change (∑ i, held d t ω i)+(∑ i, held d (t+1) ω i) ≤ _
    linarith [total_held_reference d hδ hδ' t ω,total_held_reference d hδ hδ' (t+1) ω]

theorem parent_path_budget (d : Data Ω ι k) {δ K : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hK : 1+2/δ ≤ K) (H : ℕ) (ω : Ω) :
    (∑ t ∈ range H, if parentRefresh d δ t ω then EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) ≤
      5*K*∑ t ∈ range H, |sizeEstimate (parentInput d) δ (t+1) ω-sizeEstimate (parentInput d) δ t ω| := by
  have hs := sum_le_sum (s:=range H) fun t _ => parent_step d hδ hδ' t ω
  rw [←mul_sum] at hs
  exact hs.trans ((mul_le_mul_of_nonneg_left (ParentScale.reference_charge (parentInput d) hδ hK H ω)
    (by norm_num : (0:ℝ) ≤ 5)).trans_eq (by ring))

theorem parent_budget (d : Data Ω ι k) {δ K : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/2)
    (hK : 1+2/δ ≤ K) (H : ℕ) :
    (∑ t ∈ range H, average d.weight (fun ω => if parentRefresh d δ t ω then
      EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0)) ≤
      (5*K*(5*(4/3)^2/δ))*(totalDrift (parentInput d) H+k) := by
  have ha := average_mono (fun ω => (d.positive ω).le)
    (parent_path_budget d hδ (by linarith) hK H)
  rw [average_range_sum,average_mul,average_range_sum] at ha
  have hb := sizeEstimate_budget (parentInput d) d.weight (fun ω => (d.positive ω).le)
    (fun _ => rfl) hδ hδ' H
  simp only [Fintype.card_fin] at hb
  have hK0 : 0 ≤ K := by have := div_pos (by norm_num : (0:ℝ) < 2) hδ; linarith
  exact ha.trans ((mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num) hK0)).trans_eq (by ring))

theorem size_budget (d : Data Ω ι k) (H : ℕ) :
    (∑ t ∈ range H, average d.weight (fun ω => EpochAlphaCharge.sizeCharge (held d t ω) (held d (t+1) ω))) ≤
      (2001*(5*(4/3)^2/sizeTolerance))*((∑ i, totalDrift (input d i) H)+(Fintype.card ι:ℝ)*k)+
        (Fintype.card ι:ℝ)*(5*2001*cutoff) := by
  have hs := sum_le_sum (s:=univ) fun i _ => heldSize_budget (input d i) d.weight
    (fun ω => (d.positive ω).le) d.total (fun _ => rfl) H
  simp only [EpochAlphaCharge.sizeCharge,average_sum]
  rw [sum_comm]
  convert hs using 1
  · rfl
  · simp [sum_add_distrib,←mul_sum,mul_add]
    ring

end UniformKServer.StarBudget

end


end

end OAI
