import Mathlib
import OAI.Combinatorics.UniformKServer.EpochParameters
import OAI.Combinatorics.UniformKServer.HeldRelative

namespace OAI

                                            
section

/-! Actual persistent U schedule, including changes of dominant identity.
 It has no per-epoch additive charge, and its non-wholesale changes are paid
 by held-size variation plus the existing wholesale ledger. -/
noncomputable section
namespace UniformKServer.SideReferenceSchedule
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def reset (a : ℕ → ι → ℝ) (p : ℕ → Bool) (t : ℕ) : Bool :=
  decide (AllocationEpoch.fires (EpochGeometry.scalar (EpochGeometry.schedule a p t))
    (EpochGeometry.variation (a t) (a (t+1))) (p t))

def side (a : ℕ → ι → ℝ) (p : ℕ → Bool) (t : ℕ) : ℝ :=
  match EpochGeometry.dominant (EpochGeometry.schedule a p t) with
  | none => 0
  | some o => EpochGeometry.side o (a t)

def reference (a : ℕ → ι → ℝ) (p : ℕ → Bool) : ℕ → ℝ :=
  HeldRelative.schedule (1/1000) (side a p) (reset a p)

def wholesale (a : ℕ → ι → ℝ) (p : ℕ → Bool) (t : ℕ) : ℝ :=
  if reset a p t then EpochGeometry.total (a t)+EpochGeometry.total (a (t+1)) else 0

def charge (a : ℕ → ι → ℝ) (p : ℕ → Bool) (t : ℕ) : ℝ :=
  if reset a p t then 0 else
    if reference a p t = reference a p (t+1) then 0 else side a p t+side a p (t+1)

theorem side_nonneg {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool) (t : ℕ) :
    0 ≤ side a p t := by
  unfold side
  split
  · exact le_rfl
  · exact EpochParameters.side_nonneg (ha t) _

theorem side_le_total {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (t : ℕ) : side a p t ≤ EpochGeometry.total (a t) := by
  unfold side
  split
  · exact EpochGeometry.total_nonneg (ha t)
  · rename_i o _
    rw [EpochGeometry.total_with_side (a t) o]
    linarith [ha t o]

theorem not_reset_dominant {a : ℕ → ι → ℝ} {p : ℕ → Bool} {t : ℕ}
    (h : reset a p t = false) :
    EpochGeometry.dominant (EpochGeometry.schedule a p (t+1))=
      EpochGeometry.dominant (EpochGeometry.schedule a p t) := by
  have hf : ¬ AllocationEpoch.fires (EpochGeometry.scalar (EpochGeometry.schedule a p t))
      (EpochGeometry.variation (a t) (a (t+1))) (p t) := by
    simpa only [reset,decide_eq_false_iff_not] using h
  rw [EpochGeometry.schedule,EpochGeometry.update,ite_eq_right hf]
  rfl

theorem side_difference {a : ℕ → ι → ℝ} {p : ℕ → Bool} {t : ℕ}
    (h : reset a p t=false) :
    |side a p (t+1)-side a p t| ≤ EpochGeometry.variation (a t) (a (t+1)) := by
  unfold side
  rw [not_reset_dominant h]
  split
  · simp only [sub_self,abs_zero]
    exact EpochGeometry.variation_nonneg _ _
  · exact EpochGeometry.side_difference _ _ _

theorem reference_nonneg {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (t : ℕ) : 0 ≤ reference a p t :=
  HeldRelative.schedule_nonneg (side_nonneg ha p) (reset a p) t

theorem reference_compared {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (t : ℕ) :
    AllocationSchedule.compared (1/1000) (reference a p t) (side a p t) :=
  HeldRelative.schedule_compared (by norm_num) (side_nonneg ha p) (reset a p) t

theorem reference_spec {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (t : ℕ) {o : ι}
    (ho : EpochGeometry.dominant (EpochGeometry.schedule a p t)=some o) :
    EpochParameters.sideReference (a t) o (reference a p t) := by
  have hc := reference_compared ha p t
  simp only [AllocationSchedule.compared,side,ho] at hc
  refine ⟨reference_nonneg ha p t,?_,?_⟩
  · apply (div_le_iff₀ (by norm_num : (0:ℝ)<1001/1000)).mpr
    linarith [hc.2]
  · linarith [hc.1]

theorem wholesale_budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (H : ℕ) :
    (∑ t ∈ range H, wholesale a p t) ≤
      203*(∑ t ∈ range H, EpochGeometry.variation (a t) (a (t+1)))+
      ∑ t ∈ range H, (if p t then EpochGeometry.total (a t)+EpochGeometry.total (a (t+1)) else 0) := by
  simpa only [wholesale,reset,decide_eq_true_eq,AllocationEpoch.charge] using
    EpochGeometry.wholesale_budget ha p H

theorem charge_bound {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (t : ℕ) :
    charge a p t ≤ (1001/1000)*AllocationSchedule.charge (reference a p t) (reference a p (t+1)) := by
  have hn0 := reference_nonneg ha p t
  have hn1 := reference_nonneg ha p (t+1)
  have hc := reference_compared ha p t
  unfold charge
  split_ifs with hr he
  · exact mul_nonneg (by norm_num) (by
      unfold AllocationSchedule.charge
      split_ifs
      · exact le_rfl
      · exact add_nonneg hn0 hn1)
  · rw [←he,AllocationSchedule.charge_self,mul_zero]
  · have hr' : reset a p t=false := Bool.eq_false_iff.mpr hr
    have hu : reference a p (t+1)=AllocationSchedule.relativeUpdate (1/1000)
        (reference a p t) (side a p (t+1)) := by
      simp only [reference,HeldRelative.schedule,HeldRelative.update,hr',Bool.false_eq_true,ite_false]
    rw [hu] at he ⊢
    convert HeldRelative.true_charge (by norm_num : (0:ℝ)≤1/1000)
      (side_nonneg ha p (t+1)) hc he using 1
    norm_num

theorem expenditure_bound {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (t : ℕ) :
    HeldRelative.expenditure (1/1000) 2001 (side a p) (reset a p) t ≤
      2001*EpochGeometry.variation (a t) (a (t+1))+(1001/1000)*wholesale a p t := by
  unfold HeldRelative.expenditure wholesale
  split_ifs with hr
  · have h0 := side_le_total ha p t
    have h1 := side_le_total ha p (t+1)
    have hd := EpochGeometry.variation_nonneg (a t) (a (t+1))
    nlinarith
  · have hh := side_difference (Bool.eq_false_iff.mpr hr)
    nlinarith

theorem budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (H : ℕ) :
    (∑ t ∈ range H, charge a p t) ≤
      2004*(∑ t ∈ range H, EpochGeometry.variation (a t) (a (t+1)))+
      2*(∑ t ∈ range H, wholesale a p t) := by
  have hc := sum_le_sum (s:=range H) (fun t _ => charge_bound ha p t)
  have hb := HeldRelative.budget (δ:=1/1000) (K:=2001) (by norm_num) (by norm_num)
    (side_nonneg ha p) (reset a p) H
  have he := sum_le_sum (s:=range H) (fun t _ => expenditure_bound ha p t)
  rw [←mul_sum] at hc
  rw [sum_add_distrib,←mul_sum,←mul_sum] at he
  change (∑ t ∈ range H, AllocationSchedule.charge (reference a p t) (reference a p (t+1))) ≤ _ at hb
  have hv : 0 ≤ ∑ t ∈ range H, EpochGeometry.variation (a t) (a (t+1)) :=
    sum_nonneg fun t _ => EpochGeometry.variation_nonneg _ _
  have hw : 0 ≤ ∑ t ∈ range H, wholesale a p t := by
    apply sum_nonneg
    intro t _
    unfold wholesale
    split_ifs
    · exact add_nonneg (EpochGeometry.total_nonneg (ha t)) (EpochGeometry.total_nonneg (ha (t+1)))
    · exact le_rfl
  nlinarith

end UniformKServer.SideReferenceSchedule

end


end

end OAI
