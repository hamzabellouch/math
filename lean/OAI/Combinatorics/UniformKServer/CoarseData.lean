import Mathlib
import OAI.Combinatorics.UniformKServer.RankData
import OAI.Combinatorics.UniformKServer.AllocationSchedule

namespace OAI

                                 
section

/-! Persistent size/core elementary trackers, and their actual held active
 states.  Constants and initialization allowances are uniform in the law and
 horizon. Companion §03, equations active-size-accuracy and coarse-data-budget. -/
noncomputable section
namespace UniformKServer.CoarseData
open Finset RankTracking RankData
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

def totalDrift (I : A → Input Ω) (H : ℕ) : ℝ := ∑ a, driftBudget (I a) H

def sizeEstimate (I : A → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, estimate (I a) sizeRank δ t ω

theorem sizeEstimate_nonneg (I : A → Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ sizeEstimate I δ t ω := by
  exact sum_nonneg fun a _ => sizeRank_nonneg _

theorem sizeEstimate_comparison (I : A → Input Ω) {δ : ℝ} (hδ : 0 < δ)
    (t : ℕ) (ω : Ω) :
    (1+δ)⁻¹ * totalSize (fun a => (I a).posterior t ω) ≤ sizeEstimate I δ t ω ∧
    sizeEstimate I δ t ω ≤ (1+δ) * totalSize (fun a => (I a).posterior t ω) := by
  have he (a : A) := estimate_spec (I a) sizeRank δ hδ (fun p _ => sizeRank_nonneg p) t ω
  constructor
  · rw [sizeEstimate,totalSize,mul_sum]
    exact sum_le_sum fun a _ => (he a).1
  · rw [sizeEstimate,totalSize,mul_sum]
    exact sum_le_sum fun a _ => (he a).2

theorem average_sum (w : Ω → ℝ) (X : A → Ω → ℝ) :
    average w (fun ω => ∑ a, X a ω) = ∑ a, average w (X a) := by
  simp only [average,mul_sum]
  exact sum_comm

theorem sizeEstimate_budget (I : A → Input Ω) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hi : ∀ a, (I a).weight=w)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/2) (H : ℕ) :
    (∑ t ∈ range H, average w (fun ω =>
      |sizeEstimate I δ (t+1) ω-sizeEstimate I δ t ω|)) ≤
      (5*(4/3)^2/δ)*(totalDrift I H+Fintype.card A) := by
  calc
    _ ≤ ∑ t ∈ range H, ∑ a, average w (fun ω =>
        |estimate (I a) sizeRank δ (t+1) ω-estimate (I a) sizeRank δ t ω|) := by
      apply sum_le_sum
      intro t _
      rw [← average_sum]
      apply average_mono hw
      intro ω
      rw [sizeEstimate,sizeEstimate,←sum_sub_distrib]
      exact abs_sum_le_sum_abs _ _
    _ = ∑ a, ∑ t ∈ range H, average w (fun ω =>
        |estimate (I a) sizeRank δ (t+1) ω-estimate (I a) sizeRank δ t ω|) := sum_comm
    _ ≤ ∑ a, (5*(4/3)^2/δ)*(driftBudget (I a) H+1) := by
      apply sum_le_sum
      intro a _
      rw [← hi a]
      exact (relative_tracker (I a) sizeRank δ (4/3) hδ hδ' (by norm_num)
        (fun p _ => sizeRank_nonneg p) (fun p _ q _ => sizeRank_sqrt_lipschitz p q)).2 H
    _ = _ := by simp [totalDrift,←mul_sum,sum_add_distrib]

def coreChange (I : A → Input Ω) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, if core (I a) (t+1) ω = core (I a) t ω then 0 else 1

theorem coreChange_budget (I : A → Input Ω) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hi : ∀ a, (I a).weight=w) (H : ℕ) :
    (∑ t ∈ range H, average w (coreChange I t)) ≤
      36864*(totalDrift I H+Fintype.card A) := by
  calc
    _ ≤ ∑ t ∈ range H, ∑ a, average w (fun ω =>
        if absoluteReference (I a) (RankFunctions.pstar/8) (t+1) ω =
          absoluteReference (I a) (RankFunctions.pstar/8) t ω then 0 else 1) := by
      apply sum_le_sum
      intro t _
      rw [← average_sum]
      exact average_mono hw (fun ω => sum_le_sum fun a _ => core_refresh (I a) t ω)
    _ = ∑ a, refreshCount (I a) (RankFunctions.pstar/8) H := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      simp only [refreshCount,hi a]
    _ ≤ ∑ a, 36864*(driftBudget (I a) H+1) := by
      apply sum_le_sum
      intro a _
      have h := (absolute_tracker (I a) (RankFunctions.pstar/8)
        (by norm_num [RankFunctions.pstar])).2 H
      norm_num [RankFunctions.pstar] at h
      have he : RankFunctions.pstar/8=(1/192 : ℝ) := by norm_num [RankFunctions.pstar]
      rw [he]
      exact h
    _ = _ := by simp [totalDrift,←mul_sum,sum_add_distrib]

def sizeTolerance : ℝ := 1/1000
def cutoff : ℝ := 1/10000

def activeState (I : A → Input Ω) (t : ℕ) (ω : Ω) : Option ℝ :=
  AllocationSchedule.schedule cutoff sizeTolerance (fun s => sizeEstimate I sizeTolerance s ω) t

def heldSize (I : A → Input Ω) (t : ℕ) (ω : Ω) : ℝ :=
  AllocationSchedule.size (activeState I t ω)

theorem heldSize_nonneg (I : A → Input Ω) (t : ℕ) (ω : Ω) : 0 ≤ heldSize I t ω :=
  AllocationSchedule.schedule_nonneg (fun s => sizeEstimate_nonneg I sizeTolerance s ω) t

theorem activeState_update (I : A → Input Ω) (t : ℕ) (ω : Ω) :
    ∃ s, activeState I t ω = AllocationSchedule.update cutoff sizeTolerance s
      (sizeEstimate I sizeTolerance t ω) := by
  cases t with
  | zero => exact ⟨none,rfl⟩
  | succ t => exact ⟨activeState I t ω,rfl⟩

theorem active_accuracy (I : A → Input Ω) (t : ℕ) (ω : Ω) {b : ℝ}
    (hb : activeState I t ω = some b) :
    (9/10)*totalSize (fun a => (I a).posterior t ω) ≤ b ∧
    b ≤ (11/10)*totalSize (fun a => (I a).posterior t ω) ∧
    cutoff ≤ totalSize (fun a => (I a).posterior t ω) := by
  obtain ⟨s,hs⟩ := activeState_update I t ω
  rw [hs] at hb
  have hd := AllocationSchedule.update_active (by norm_num [cutoff])
    (by norm_num [sizeTolerance]) (sizeEstimate_nonneg I sizeTolerance t ω) s hb
  have hm := sizeEstimate_comparison I (show 0 < sizeTolerance by norm_num [sizeTolerance]) t ω
  have hn : 0 ≤ totalSize (fun a => (I a).posterior t ω) := sum_nonneg fun a _ => sizeRank_nonneg _
  norm_num [sizeTolerance,cutoff,AllocationSchedule.compared] at *
  constructor
  · linarith
  constructor <;> linarith

theorem inactive_small (I : A → Input Ω) (t : ℕ) (ω : Ω)
    (hb : activeState I t ω = none) :
    totalSize (fun a => (I a).posterior t ω) ≤ 10*cutoff := by
  obtain ⟨s,hs⟩ := activeState_update I t ω
  rw [hs] at hb
  have hd := AllocationSchedule.update_inactive (by norm_num [cutoff]) s hb
  have hm := (sizeEstimate_comparison I (show 0 < sizeTolerance by norm_num [sizeTolerance]) t ω).1
  norm_num [sizeTolerance,cutoff] at *
  linarith

theorem inactive_zero (I : A → Input Ω) (t : ℕ) (ω : Ω) (β : ℝ)
    (hb : activeState I t ω = none) :
    coreCount (fun a => core (I a) t ω) = 0 ∧
    totalRank β (fun a => (I a).posterior t ω) = 0 ∧
    flex (fun a => core (I a) t ω) β (fun a => (I a).posterior t ω) = 0 := by
  apply inactive_ranks
  · intro a ha
    have := core_small (I a) t ω ha
    norm_num [RankFunctions.pstar] at *
    linarith
  · have := inactive_small I t ω hb
    norm_num [cutoff] at *
    exact this

theorem heldSize_path_budget (I : A → Input Ω) (H : ℕ) (ω : Ω) :
    (∑ t ∈ range H, AllocationSchedule.charge (heldSize I t ω) (heldSize I (t+1) ω)) ≤
    2001*(∑ t ∈ range H, |sizeEstimate I sizeTolerance (t+1) ω-sizeEstimate I sizeTolerance t ω|)+
      5*2001*cutoff := by
  have h := AllocationSchedule.schedule_budget (show 0 ≤ cutoff by norm_num [cutoff])
    (show 0 < sizeTolerance by norm_num [sizeTolerance]) (show (3:ℝ) ≤ 2001 by norm_num)
    (show 1+2/sizeTolerance ≤ 2001 by norm_num [sizeTolerance])
    (fun s => sizeEstimate_nonneg I sizeTolerance s ω) H
  have hi := AllocationSchedule.initial_potential_bound (δ:=sizeTolerance)
    (show 0 ≤ cutoff by norm_num [cutoff]) (show (1:ℝ) ≤ 2001 by norm_num)
    (sizeEstimate_nonneg I sizeTolerance 0 ω)
  change _ ≤ _ + AllocationSchedule.potential 2001 cutoff (sizeEstimate I sizeTolerance 0 ω)
    (AllocationSchedule.update cutoff sizeTolerance none (sizeEstimate I sizeTolerance 0 ω)) at h
  exact h.trans (by linarith [hi])


theorem average_range_sum (w : Ω → ℝ) (X : ℕ → Ω → ℝ) (H : ℕ) :
    average w (fun ω => ∑ t ∈ range H, X t ω) = ∑ t ∈ range H, average w (X t) := by
  simp only [average,mul_sum]
  exact sum_comm

theorem average_const (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (c : ℝ) :
    average w (fun _ => c) = c := by rw [average,←sum_mul,hw,one_mul]

theorem heldSize_budget (I : A → Input Ω) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (htotal : ∑ ω, w ω=1)
    (hi : ∀ a, (I a).weight=w) (H : ℕ) :
    (∑ t ∈ range H, average w (fun ω =>
      AllocationSchedule.charge (heldSize I t ω) (heldSize I (t+1) ω))) ≤
      (2001*(5*(4/3)^2/sizeTolerance))*(totalDrift I H+Fintype.card A)+5*2001*cutoff := by
  have h := average_mono hw (heldSize_path_budget I H)
  rw [average_range_sum,average_add,average_mul,average_const w htotal,average_range_sum] at h
  have hb := sizeEstimate_budget I w hw hi (show 0 < sizeTolerance by norm_num [sizeTolerance])
    (show sizeTolerance < 1/2 by norm_num [sizeTolerance]) H
  nlinarith

theorem sizeEstimate_measurable (I : A → Input Ω) (F : ℕ → Setoid Ω)
    (hF : ∀ a, (I a).filtration=F) (δ : ℝ) (t : ℕ) :
    measurableAt F t (sizeEstimate I δ t) := by
  intro ω v hv
  apply sum_congr rfl
  intro a _
  have ha : ((I a).filtration t).r ω v := by rw [hF a]; exact hv
  have hr := reference_measurable (I a) sizeRank δ t ω v ha
  simp only [estimate,hr]

theorem activeState_measurable (I : A → Input Ω) (F : ℕ → Setoid Ω)
    (hF : ∀ a, (I a).filtration=F)
    (hRef : ∀ t ω v, (F (t+1)).r ω v → (F t).r ω v) :
    ∀ t ω v, (F t).r ω v → activeState I t ω = activeState I t v := by
  intro t
  induction t with
  | zero =>
    intro ω v hv
    have hx := sizeEstimate_measurable I F hF sizeTolerance 0 ω v hv
    simp only [activeState,AllocationSchedule.schedule,hx]
  | succ t ih =>
    intro ω v hv
    have hx := sizeEstimate_measurable I F hF sizeTolerance (t+1) ω v hv
    have hs := ih ω v (hRef t ω v hv)
    change AllocationSchedule.update cutoff sizeTolerance (activeState I t ω)
      (sizeEstimate I sizeTolerance (t+1) ω) =
      AllocationSchedule.update cutoff sizeTolerance (activeState I t v)
      (sizeEstimate I sizeTolerance (t+1) v)
    rw [hx,hs]

end UniformKServer.CoarseData

end


end

end OAI
