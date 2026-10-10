import Mathlib
import OAI.Combinatorics.UniformKServer.ActualFineCaps
import OAI.Combinatorics.UniformKServer.StarSchedules
import OAI.Combinatorics.UniformKServer.StarConstants

namespace OAI

                               
section

/-! The source's fine caps, instantiated with absolute tolerances and the
actual causal held-size epochs. Endpoint trackers are never restarted. -/
noncomputable section
namespace UniformKServer.StarCaps
open Finset StarRanks StarSchedules RankTracking RankData CoarseData FlexEstimates
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def factor (s : EpochGeometry.State ι) (k : ℕ) (i : ι) : ℝ :=
  if EpochGeometry.dominant s=some i then 1+StarConstants.lam/EpochAlpha.ell k
  else 1-StarConstants.lam/EpochAlpha.ell k

def flex (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  factor (epoch d StarConstants.delta t ω) k i * estimateFlex (input d i)
    (upper d StarConstants.delta t ω) (StarConstants.rho/EpochAlpha.ell k) t ω

def cap (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  coreCount (flags d t ω i)+flex d t ω i

def wholesale (d : Data Ω ι k) (t : ℕ) (ω : Ω) : Bool :=
  SideReferenceSchedule.reset (fun s => held d s ω) (fun s => parentRefresh d StarConstants.delta s ω) t

theorem tolerance (k : ℕ) :
    0 < StarConstants.rho/EpochAlpha.ell k ∧ StarConstants.rho/EpochAlpha.ell k < 1/2 := by
  have h := EpochAlpha.ell_one k
  have hp : 0 < EpochAlpha.ell k := by linarith
  refine ⟨div_pos StarConstants.rho_bounds.1 hp, (div_lt_iff₀ hp).2 ?_⟩
  linarith [StarConstants.rho_bounds.2]

theorem factor_range (s : EpochGeometry.State ι) (k : ℕ) (i : ι) :
    factor s k i ∈ Set.Icc (0:ℝ) 2 := by
  have h := EpochAlpha.ell_one k
  have hp : 0 < EpochAlpha.ell k := by linarith
  have h0 := div_nonneg StarConstants.lam_bounds.1.le hp.le
  have h1 : StarConstants.lam/EpochAlpha.ell k ≤ 1/4 := by
    apply (div_le_iff₀ hp).2
    linarith [StarConstants.lam_bounds.2]
  unfold factor
  split_ifs <;> constructor <;> linarith

theorem cap_eq (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    cap d t ω i = FineVariation.cap (input d i) (upper d StarConstants.delta t ω)
      (StarConstants.rho/EpochAlpha.ell k) (factor (epoch d StarConstants.delta t ω) k i) t ω := rfl

theorem cap_nonneg (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    0 ≤ cap d t ω i := by
  rw [cap_eq]
  exact ActualFineCaps.cap_nonneg _ (upper_allowed d StarConstants.delta_bounds.1 hk t ω)
    (factor_range _ k i).1 _ _ _

theorem cap_bound (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    cap d t ω i ≤ 120*held d t ω i := by
  rw [cap_eq]
  exact ActualFineCaps.cap_bound _ (upper_allowed d StarConstants.delta_bounds.1 hk t ω)
    (tolerance k).1 (tolerance k).2.le (factor_range _ k i) _ _

theorem inactive_cap (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : held d t ω i=0) : cap d t ω i=0 := by
  have h := cap_bound d hk t ω i
  rw [hi,mul_zero] at h
  exact le_antisymm h (cap_nonneg d hk t ω i)

theorem regular (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (ha : 0 < held d t ω i) (hi : EpochGeometry.dominant (epoch d StarConstants.delta t ω) ≠ some i) :
    trueFlex (input d i) (ParentBeta.trueParam (input d i) k t ω) t ω ≤ flex d t ω i ∧
      flex d t ω i ≤ trueFlex (input d i) (ParentBeta.trueParam (parentInput d) k t ω) t ω := by
  simp only [flex,factor,ite_eq_right hi]
  exact ActualFineCaps.regular_comparison d hk StarConstants.delta_bounds.1 StarConstants.rho_bounds.1
    StarConstants.lam_bounds.1.le StarConstants.lam_bounds.2 StarConstants.fine_error
    StarConstants.fine_gap StarConstants.fine_eps t ω _ (epoch_valid d _ t ω) i ha hi

theorem dominant (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some i) :
    trueFlex (input d i) (ParentBeta.trueParam (parentInput d) k t ω) t ω ≤ flex d t ω i ∧
      flex d t ω i ≤ (1+StarConstants.eps/EpochAlpha.ell k)*
        trueFlex (input d i) (ParentBeta.trueParam (parentInput d) k t ω) t ω := by
  have hb := ParentBeta.true_allowed (parentInput d) hk t ω (parent_size_bound d t ω)
  have he0 : 0 ≤ StarConstants.rho+4*ParentBeta.cBeta*StarConstants.delta := by
    norm_num [StarConstants.rho,ParentBeta.cBeta,StarConstants.delta]
  have h := (FineCaps.caps (γ:=4*StarConstants.lam)
    (f:=(1-4*StarConstants.lam/EpochAlpha.ell k)*trueFlex (input d i)
      (ParentBeta.trueParam (parentInput d) k t ω) t ω)
    (EpochAlpha.ell_one k) StarConstants.lam_bounds.1.le StarConstants.lam_bounds.2
    he0 StarConstants.fine_error le_rfl StarConstants.fine_eps (flex_nonneg _ hb t ω)
    (ActualFineCaps.held_error d hk StarConstants.delta_bounds.1 StarConstants.rho_bounds.1 t ω i) le_rfl).2
  simpa only [flex,factor,ite_eq_left hi,upper] using h

theorem deficit_comparison (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some i) :
    trueFlex (input d i) (ParentBeta.trueParam (parentInput d) k t ω) t ω/2 ≤ deficit d StarConstants.delta t ω ∧
      deficit d StarConstants.delta t ω ≤ 2*trueFlex (input d i) (ParentBeta.trueParam (parentInput d) k t ω) t ω := by
  simp only [deficit,hi]
  exact ActualFineCaps.coarse_comparison _ (ParentBeta.true_allowed (parentInput d) hk t ω (parent_size_bound d t ω)) t ω

theorem not_wholesale_parent (d : Data Ω ι k) (t : ℕ) (ω : Ω) (h : wholesale d t ω=false) :
    parentRefresh d StarConstants.delta t ω=false := by
  have hf : ¬ AllocationEpoch.fires (EpochGeometry.scalar (epoch d StarConstants.delta t ω))
      (EpochGeometry.variation (held d t ω) (held d (t+1) ω)) (parentRefresh d StarConstants.delta t ω) := by
    simpa only [wholesale,SideReferenceSchedule.reset,epoch,decide_eq_false_iff_not] using h
  unfold AllocationEpoch.fires at hf
  exact Bool.eq_false_iff.mpr (fun hp => hf (Or.inl hp))

theorem not_wholesale_upper (d : Data Ω ι k) (t : ℕ) (ω : Ω) (h : wholesale d t ω=false) :
    upper d StarConstants.delta (t+1) ω=upper d StarConstants.delta t ω := by
  have hp := not_wholesale_parent d t ω h
  have he : ParentScale.reference (parentInput d) StarConstants.delta (t+1) ω=
      ParentScale.reference (parentInput d) StarConstants.delta t ω := by
    simpa only [parentRefresh,decide_eq_false_iff_not,not_not] using hp
  simp only [upper,ParentBeta.heldParam,ParentScale.lowerX,he]

theorem not_wholesale_factor (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) (h : wholesale d t ω=false) :
    factor (epoch d StarConstants.delta (t+1) ω) k i=factor (epoch d StarConstants.delta t ω) k i := by
  have hd := SideReferenceSchedule.not_reset_dominant h
  change EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=
    EpochGeometry.dominant (epoch d StarConstants.delta t ω) at hd
  simp only [factor,hd]

theorem cap_step (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) (h : wholesale d t ω=false) :
    |cap d (t+1) ω i-cap d t ω i| ≤
      2*FineVariation.endpointVariation (input d i) (StarConstants.rho/EpochAlpha.ell k) t ω+
      3*coreChange (input d i) t ω := by
  rw [cap_eq,cap_eq,not_wholesale_upper d t ω h,not_wholesale_factor d t ω i h]
  exact FineVariation.cap_step _ (upper_allowed d StarConstants.delta_bounds.1 hk t ω)
    (factor_range _ k i) _ t ω

end UniformKServer.StarCaps

end


end

end OAI
