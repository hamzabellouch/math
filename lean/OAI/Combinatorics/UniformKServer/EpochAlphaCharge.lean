import Mathlib
import OAI.Combinatorics.UniformKServer.AlphaPrepared
import OAI.Combinatorics.UniformKServer.EpochAlphaStatic

namespace OAI

                                       
section

/-! Actual epoch schedule charging of the prepared alpha jump. The zero core
mass branch is free; sparse refreshes and wholesale charges are distinct. -/
noncomputable section
namespace UniformKServer.EpochAlphaCharge
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def sizeCharge (a b : ι → ℝ) : ℝ := ∑ i, AllocationSchedule.charge (a i) (b i)
def param (a : ℕ → ι → ℝ) (p : ℕ → Bool) (ell ct C : ℝ) (t : ℕ) : AlphaEmpty.Config ι :=
  EpochAlphaSchedule.config (a t) (EpochGeometry.schedule a p t) (SideReferenceSchedule.reference a p t) ell ct C

omit [Fintype ι] in
theorem eta_le {P : AlphaEmpty.Config ι} (hp : AlphaEmpty.valid P) (i : ι) : AlphaEmpty.eta P i ≤ 1 := by
  cases P with
  | none => norm_num [AlphaEmpty.eta]
  | some P =>
    change DomainTransport.extend P.active (ProportionParameters.eta P.param) i ≤ 1
    unfold DomainTransport.extend
    split_ifs with hi
    · exact hp.2.2.2.2.1 ⟨i,hi⟩
    · norm_num

theorem side_nonneg (a : ℕ → ι → ℝ) (p : ℕ → Bool) (ha : ∀ t i, 0 ≤ a t i) (t : ℕ) :
    0 ≤ SideReferenceSchedule.charge a p t := by
  unfold SideReferenceSchedule.charge
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · exact add_nonneg (SideReferenceSchedule.side_nonneg ha p t) (SideReferenceSchedule.side_nonneg ha p (t+1))

theorem size_nonneg {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) : 0 ≤ sizeCharge a b := by
  apply sum_nonneg
  intro i _
  unfold AllocationSchedule.charge
  split_ifs
  · exact le_rfl
  · exact add_nonneg (ha i) (hb i)

theorem sparse {a b B : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hB : ∀ i, B i ≤ 40*b i) :
    (∑ i, if a i=b i then 0 else B i) ≤ 40*sizeCharge a b := by
  rw [sizeCharge,mul_sum]
  apply sum_le_sum
  intro i _
  unfold AllocationSchedule.charge
  split_ifs
  · norm_num
  · linarith [hB i,ha i]

theorem not_reset_base {a : ℕ → ι → ℝ} {p : ℕ → Bool} {t : ℕ}
    (h : SideReferenceSchedule.reset a p t=false) :
    (EpochGeometry.schedule a p t).base=(EpochGeometry.schedule a p (t+1)).base := by
  have hf : ¬AllocationEpoch.fires (EpochGeometry.scalar (EpochGeometry.schedule a p t))
      (EpochGeometry.variation (a t) (a (t+1))) (p t) := by
    simpa only [SideReferenceSchedule.reset,decide_eq_false_iff_not] using h
  rw [EpochGeometry.schedule,EpochGeometry.update,ite_eq_right hf]

theorem jump {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool)
    {ell ct C : ℝ} (hsc : 0 ≤ C*ell) (hct : ct/ell ≤ 1)
    (hp : ∀ t, AlphaEmpty.valid (param a p ell ct C t)) (t : ℕ) (B v : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hBb : ∀ i, B i ≤ 40*a (t+1) i)
    (hpa : DomainTransport.Supported (AlphaEmpty.active (param a p ell ct C t)) B)
    (hqa : DomainTransport.Supported (AlphaEmpty.active (param a p ell ct C (t+1))) B)
    (hv : AlphaEmpty.state (param a p ell ct C (t+1)) v)
    (hf : ∀ i, (∑ j, B j)*v i ≤ (1+AlphaEmpty.eta (param a p ell ct C t) i)*B i) :
    |AlphaEmpty.potential (param a p ell ct C (t+1)) B v-
      AlphaEmpty.potential (param a p ell ct C t) B v| ≤
      320*(C*ell)*sizeCharge (a t) (a (t+1))+
      1600*(C*ell)*SideReferenceSchedule.charge a p t+
      1200*(C*ell)*SideReferenceSchedule.wholesale a p t := by
  have hsz := size_nonneg (ha t) (ha (t+1))
  have hsd := side_nonneg a p ha t
  have ht0 := EpochGeometry.total_nonneg (ha t)
  have ht1 := EpochGeometry.total_nonneg (ha (t+1))
  by_cases hr : SideReferenceSchedule.reset a p t=true
  · have hh := AlphaPrepared.jump (hp t) (hp (t+1)) B v hB hpa hqa hv hf
    have hs0 := EpochAlphaJump.scale_bound (a t) (EpochGeometry.schedule a p t)
      (SideReferenceSchedule.reference a p t) ell ct C hsc
    have hs1 := EpochAlphaJump.scale_bound (a (t+1)) (EpochGeometry.schedule a p (t+1))
      (SideReferenceSchedule.reference a p (t+1)) ell ct C hsc
    change AlphaEmpty.scale (param a p ell ct C t) ≤ C*ell at hs0
    change AlphaEmpty.scale (param a p ell ct C (t+1)) ≤ C*ell at hs1
    have hS : 0 ≤ ∑ i, B i := sum_nonneg fun i _ => hB i
    have hsb := sum_le_sum (s:=univ) (fun i _ => hBb i)
    rw [←mul_sum] at hsb
    change _ ≤ 40*EpochGeometry.total (a (t+1)) at hsb
    have h1 := mul_le_mul_of_nonneg_right (add_le_add hs0 hs1) hS
    have h2 := mul_le_mul_of_nonneg_left hsb hsc
    have h3 := mul_nonneg hsc ht0
    have hz := mul_nonneg hsc hsz
    have hside := mul_nonneg hsc hsd
    rw [SideReferenceSchedule.wholesale,ite_eq_left hr]
    nlinarith
  · have hr' := Bool.eq_false_iff.mpr hr
    rw [SideReferenceSchedule.wholesale,ite_eq_right hr,mul_zero,add_zero]
    have hS : 0 ≤ ∑ i, B i := sum_nonneg fun i _ => hB i
    rcases hS.eq_or_lt with hz | hpos
    · have he := AlphaPrepared.zero_of_sum hB hz.symm
      rw [he,AlphaEmpty.potential_zero,AlphaEmpty.potential_zero,sub_self,abs_zero]
      positivity
    · have hs := EpochGeometry.schedule_valid ha p t
      have hs' := EpochGeometry.schedule_valid ha p (t+1)
      have he := not_reset_base hr'
      have hpa' : DomainTransport.Supported (EpochParameters.active (a t)) B := by
        simpa only [param,EpochAlphaSchedule.active_eq hs] using hpa
      have hqa' : DomainTransport.Supported (EpochParameters.active (a (t+1))) B := by
        simpa only [param,EpochAlphaSchedule.active_eq hs'] using hqa
      have hsum : ∑ i, v i=1 := by
        cases heq : param a p ell ct C (t+1) with
        | none =>
          have hzB : B=fun _ => 0 := AlphaEmpty.zero_supported (by simpa only [heq,AlphaEmpty.active] using hqa)
          simp only [hzB,sum_const_zero,lt_self_iff_false] at hpos
        | some q =>
          rw [heq] at hv
          exact hv.2.2
      have hf2 (i : ι) : (∑ j, B j)*v i ≤ 2*B i := by
        have hh := mul_le_mul_of_nonneg_right (eta_le (hp t) i) (hB i)
        nlinarith [hf i]
      have hh := EpochAlphaStatic.same_epoch (ha t) (ha (t+1)) hs hs' he hsc hct
        (fun o ho => SideReferenceSchedule.reference_spec ha p t ho)
        (fun o ho => SideReferenceSchedule.reference_spec ha p (t+1) ho)
        (hp t) (hp (t+1)) v hpos hB hBb hpa' hqa' (AlphaEmpty.state_interval hv) hsum hf2
      have hc : (if SideReferenceSchedule.reference a p t=SideReferenceSchedule.reference a p (t+1) then 0
          else match EpochGeometry.dominant (EpochGeometry.schedule a p t) with
          | none => 0
          | some o => 1600*(C*ell)*(EpochGeometry.side o (a t)+EpochGeometry.side o (a (t+1)))) =
          1600*(C*ell)*SideReferenceSchedule.charge a p t := by
        unfold SideReferenceSchedule.charge SideReferenceSchedule.side
        rw [ite_eq_right hr,SideReferenceSchedule.not_reset_dominant hr']
        split_ifs
        · ring
        · cases hd : EpochGeometry.dominant (EpochGeometry.schedule a p t) <;> ring
      have hsp := mul_le_mul_of_nonneg_left (sparse (ha t) hBb) hsc
      calc
        _ ≤ 8*(C*ell)*(∑ i, if a t i=a (t+1) i then 0 else B i)+
            (if SideReferenceSchedule.reference a p t=SideReferenceSchedule.reference a p (t+1) then 0
            else match EpochGeometry.dominant (EpochGeometry.schedule a p t) with
            | none => 0
            | some o => 1600*(C*ell)*(EpochGeometry.side o (a t)+EpochGeometry.side o (a (t+1)))) := hh
        _ = 8*(C*ell)*(∑ i, if a t i=a (t+1) i then 0 else B i)+
            1600*(C*ell)*SideReferenceSchedule.charge a p t := congrArg (fun z => _+z) hc
        _ ≤ _ := by nlinarith


end UniformKServer.EpochAlphaCharge

end


end

end OAI
