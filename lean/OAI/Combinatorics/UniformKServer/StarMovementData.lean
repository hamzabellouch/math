import Mathlib
import OAI.Combinatorics.UniformKServer.StarAllocator

namespace OAI

                                       
section

/-! Actual scalar bounds and epoch cases for the coefficient-one output
movement estimate.  No unproved tracker ledger occurs in these hypotheses. -/
noncomputable section
namespace UniformKServer.StarMovementData
open Finset StarRanks StarSchedules StarLower StarOutputData StarOutputFeasibility StarAllocator
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem eps_bound (k : ℕ) : 0 ≤ StarConstants.eps/EpochAlpha.ell k ∧
    StarConstants.eps/EpochAlpha.ell k ≤ 1/100 := by
  have he := EpochAlpha.ell_one k
  have hp : 0 < EpochAlpha.ell k := by linarith
  refine ⟨div_nonneg (by norm_num [StarConstants.eps]) hp.le,(div_le_iff₀ hp).2 ?_⟩
  norm_num [StarConstants.eps]
  linarith

theorem holes_one (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) (hreg : deficit d StarConstants.delta t ω/2 ≤ StarOutputData.mass d t ω) :
    AllocationOutputs.excess (StarCaps.cap d t ω) q ≤ 4*StarOutputData.mass d t ω := by
  have h := required_holes d hk t ω hq
  have he := error_rule_one d hk t ω hreg
  have hc : parentBeta d t ω+4*StarConstants.eps/EpochAlpha.ell k ≤ 4 := by
    have hb := (parent_allowed d hk t ω).2
    have hc := (eps_bound k).2
    rw [mul_div_assoc]
    linarith
  have hm := mul_le_mul_of_nonneg_right hc (mass_nonneg d t ω)
  nlinarith only [h,he,hm]

theorem holes_down (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) (o : ι)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some o)
    (hreg : StarOutputData.mass d t ω ≤ deficit d StarConstants.delta t ω/2) :
    AllocationOutputs.excess (StarCaps.cap d t ω) q ≤ 4*deficit d StarConstants.delta t ω := by
  have h := required_holes d hk t ω hq
  have he := (StarCaps.dominant d hk t ω o ho).2
  have hD := (StarCaps.deficit_comparison d hk t ω o ho).1
  change parentFlex d t ω o/2 ≤ _ at hD
  change StarCaps.flex d t ω o ≤ (1+StarConstants.eps/EpochAlpha.ell k)*parentFlex d t ω o at he
  have he' : error d t ω ≤ 2*(StarConstants.eps/EpochAlpha.ell k)*deficit d StarConstants.delta t ω := by
    simp only [error,ho]
    have hh := mul_le_mul_of_nonneg_left (show parentFlex d t ω o ≤ 2*deficit d StarConstants.delta t ω by linarith) (eps_bound k).1
    nlinarith only [he,hh]
  have hb := parent_allowed d hk t ω
  have hm := mul_le_mul_of_nonneg_left hreg (show 0 ≤ parentBeta d t ω by linarith [hb.1])
  have hc : parentBeta d t ω/2+2*(StarConstants.eps/EpochAlpha.ell k) ≤ 4 := by
    linarith [hb.2,(eps_bound k).2]
  have hh := mul_le_mul_of_nonneg_right hc (deficit_nonneg d StarConstants.delta t ω)
  nlinarith only [h,he',hm,hh]

theorem side_sum (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    (∑ i, side d hk t ω i) ≤ 11 := (SideFiniteInput.tracker_state (sideData d hk) t ω).2.2

theorem epoch_base (d : Data Ω ι k) (t : ℕ) (ω : Ω) (h : StarCaps.wholesale d t ω=false) :
    (epoch d StarConstants.delta (t+1) ω).base=(epoch d StarConstants.delta t ω).base := by
  have hf : ¬ AllocationEpoch.fires (EpochGeometry.scalar (epoch d StarConstants.delta t ω))
      (EpochGeometry.variation (held d t ω) (held d (t+1) ω)) (parentRefresh d StarConstants.delta t ω) := by
    simpa only [StarCaps.wholesale,SideReferenceSchedule.reset,epoch,decide_eq_false_iff_not] using h
  change (EpochGeometry.update (epoch d StarConstants.delta t ω) (held d t ω) (held d (t+1) ω)
    (parentRefresh d StarConstants.delta t ω)).base=_
  rw [EpochGeometry.update,ite_eq_right hf]

theorem empty_next (d : Data Ω ι k) (t : ℕ) (ω : Ω) (h : StarCaps.wholesale d t ω=false)
    (hz : ∀ i, held d t ω i=0) : ∀ i, held d (t+1) ω i=0 := by
  have h₀ := (EpochGeometry.total_comparison (epoch_valid d StarConstants.delta t ω)).1
  have h₁ := (EpochGeometry.total_comparison (epoch_valid d StarConstants.delta (t+1) ω)).2
  rw [epoch_base d t ω h] at h₁
  have hsum : EpochGeometry.total (held d t ω)=0 := by simp [EpochGeometry.total,hz]
  rw [hsum] at h₀
  intro i
  have hi : held d (t+1) ω i ≤ EpochGeometry.total (held d (t+1) ω) :=
    single_le_sum (fun j _ => held_nonneg d (t+1) ω j) (mem_univ i)
  exact le_antisymm (by linarith) (held_nonneg d (t+1) ω i)

theorem dominant_active (d : Data Ω ι k) (t : ℕ) (ω : Ω) (o : ι)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some o) : 0 < held d t ω o := by
  have hp := (EpochGeometry.dominant_spec ho).1
  have hh := (EpochGeometry.dominant_size (epoch_valid d StarConstants.delta t ω) ho).1
  linarith

theorem tag_step (d : Data Ω ι k) (t : ℕ) (ω : Ω) (h : StarCaps.wholesale d t ω=false) :
    tag d (t+1) ω=SwitchTracker.update (tag d t ω) (StarOutputData.mass d (t+1) ω) (deficit d StarConstants.delta (t+1) ω) := by
  change SwitchFinite.rule (switchData d) (t+1) ω=_
  rw [SwitchFinite.rule]
  change SwitchTracker.update (if StarCaps.wholesale d t ω then .one else tag d t ω) _ _=_
  rw [h]
  rfl

def charge (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ := SwitchFinite.charge (switchData d) t ω

theorem charge_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) : 0 ≤ charge d t ω := by
  unfold charge SwitchFinite.charge
  split
  · exact le_rfl
  · exact SwitchTracker.charge_nonneg _ (mass_nonneg d (t+1) ω) (deficit_nonneg d StarConstants.delta (t+1) ω)

theorem charge_step (d : Data Ω ι k) (t : ℕ) (ω : Ω) (h : StarCaps.wholesale d t ω=false) :
    charge d t ω=SwitchTracker.charge (tag d t ω) (StarOutputData.mass d (t+1) ω) (deficit d StarConstants.delta (t+1) ω) := by
  change (if StarCaps.wholesale d t ω then 0 else _) = _
  rw [h]
  rfl

end UniformKServer.StarMovementData

end


end

end OAI
