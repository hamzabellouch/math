import Mathlib
import OAI.Combinatorics.UniformKServer.FlexEstimates
import OAI.Combinatorics.UniformKServer.CoarseData

namespace OAI

                                    
section

/-! Fine endpoint movement is charged once, without the logarithmic weight
of the proportion potentials. Trackers continue through every epoch. -/
noncomputable section
namespace UniformKServer.FineVariation
open Finset RankFunctions RankData RankTracking FlexEstimates CoarseData
open scoped Classical
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

def endpointVariation (I : A → Input Ω) (ξ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, (|estimate (I a) (rank 3) ξ (t+1) ω-estimate (I a) (rank 3) ξ t ω|+
    |estimate (I a) (rank (3+1/100)) ξ (t+1) ω-estimate (I a) (rank (3+1/100)) ξ t ω|)

theorem masked_noncore (a b : Bool) {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) :
    |(if b then 0 else y)-(if a then 0 else x)| ≤ |y-x|+(if b=a then 0 else 1) := by
  cases a <;> cases b
  · simp
  · simp only [Bool.false_eq_true,ite_false,ite_true,zero_sub,abs_neg,Bool.true_eq_false]
    rw [abs_of_nonneg hx.1]
    linarith [abs_nonneg (y-x),hx.2,hy.2]
  · simp only [Bool.false_eq_true,ite_false,ite_true,sub_zero]
    rw [abs_of_nonneg hy.1]
    linarith [abs_nonneg (y-x),hx.2,hy.2]
  · simp only [ite_true,sub_self,abs_zero,add_zero]
    exact abs_nonneg _

theorem flex_step (I : A → Input Ω) {β : ℝ} (hβ : allowed β) (ξ : ℝ) (t : ℕ) (ω : Ω) :
    |estimateFlex I β ξ (t+1) ω-estimateFlex I β ξ t ω| ≤
      endpointVariation I ξ t ω+coreChange I t ω := by
  unfold estimateFlex
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  unfold endpointVariation coreChange
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro a _
  have hm := masked_noncore (core (I a) t ω) (core (I a) (t+1) ω)
    (term_range (I a) hβ ξ t ω) (term_range (I a) hβ ξ (t+1) ω)
  have ht := FineCaps.interpolation_variation (a:=estimate (I a) (rank 3) ξ t ω)
    (b:=estimate (I a) (rank (3+1/100)) ξ t ω)
    (A:=estimate (I a) (rank 3) ξ (t+1) ω)
    (B:=estimate (I a) (rank (3+1/100)) ξ (t+1) ω) (mix_range hβ)
  apply hm.trans
  change |term (I a) β ξ (t+1) ω-term (I a) β ξ t ω| + _ ≤ _
  unfold term
  exact add_le_add ht le_rfl

theorem core_step (I : A → Input Ω) (t : ℕ) (ω : Ω) :
    |coreCount (fun a => core (I a) (t+1) ω)-coreCount (fun a => core (I a) t ω)| ≤
      coreChange I t ω := by
  unfold coreCount
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro a _
  cases ha : core (I a) t ω <;> cases hb : core (I a) (t+1) ω <;> simp [ha,hb]

theorem endpoint_budget (I : A → Input Ω) (w : Ω → ℝ) (hi : ∀ a, (I a).weight=w)
    {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 1/2) (H : ℕ) :
    (∑ t ∈ range H, average w (endpointVariation I ξ t)) ≤
      (160/ξ)*(totalDrift I H+Fintype.card A) := by
  have he (β : ℝ) (hβ : allowed β) :
      (∑ a, ∑ t ∈ range H, average w (fun ω =>
        |estimate (I a) (rank β) ξ (t+1) ω-estimate (I a) (rank β) ξ t ω|)) ≤
      (80/ξ)*(totalDrift I H+Fintype.card A) := by
    calc
      _ ≤ ∑ a, (80/ξ)*(driftBudget (I a) H+1) := by
        apply sum_le_sum
        intro a _
        rw [←hi a]
        have h := (relative_tracker (I a) (rank β) ξ 4 hξ hξ' (by norm_num)
          (fun _ _ => rank_nonneg hβ) (fun _ hp _ hq => sqrt_rank_lipschitz hβ hp.1 hq.1)).2 H
        norm_num at h
        exact h
      _ = _ := by simp [totalDrift,←mul_sum,sum_add_distrib]
  have h0 := he 3 (by norm_num [allowed])
  have h1 := he (3+1/100) (by norm_num [allowed])
  have hid : (∑ t ∈ range H, average w (endpointVariation I ξ t)) =
      (∑ a, ∑ t ∈ range H, average w (fun ω =>
        |estimate (I a) (rank 3) ξ (t+1) ω-estimate (I a) (rank 3) ξ t ω|))+
      (∑ a, ∑ t ∈ range H, average w (fun ω =>
        |estimate (I a) (rank (3+1/100)) ξ (t+1) ω-estimate (I a) (rank (3+1/100)) ξ t ω|)) := by
    change (∑ t ∈ range H, average w (fun ω => ∑ a, _)) = _
    simp_rw [average_sum,average_add]
    rw [sum_comm (s:=range H)]
    simp_rw [sum_add_distrib]
  rw [hid,show (160:ℝ)/ξ=80/ξ+80/ξ by ring,add_mul]
  exact add_le_add h0 h1

def cap (I : A → Input Ω) (β ξ factor : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  coreCount (fun a => core (I a) t ω)+factor*estimateFlex I β ξ t ω

theorem cap_step (I : A → Input Ω) {β factor : ℝ} (hβ : allowed β)
    (hf : factor ∈ Set.Icc (0:ℝ) 2) (ξ : ℝ) (t : ℕ) (ω : Ω) :
    |cap I β ξ factor (t+1) ω-cap I β ξ factor t ω| ≤
      2*endpointVariation I ξ t ω+3*coreChange I t ω := by
  calc
    _ = |(coreCount (fun a => core (I a) (t+1) ω)-coreCount (fun a => core (I a) t ω))+
      factor*(estimateFlex I β ξ (t+1) ω-estimateFlex I β ξ t ω)| := by unfold cap; congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ coreChange I t ω+2*|estimateFlex I β ξ (t+1) ω-estimateFlex I β ξ t ω| := by
      rw [abs_mul,abs_of_nonneg hf.1]
      exact add_le_add (core_step I t ω) (mul_le_mul_of_nonneg_right hf.2 (abs_nonneg _))
    _ ≤ _ := by linarith [flex_step I hβ ξ t ω]

end UniformKServer.FineVariation

end


end

end OAI
