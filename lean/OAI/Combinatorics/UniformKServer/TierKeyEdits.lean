import Mathlib
import OAI.Combinatorics.UniformKServer.KeyEdits
import OAI.Combinatorics.UniformKServer.TierRetirement
import OAI.Combinatorics.UniformKServer.SortedRoster

namespace OAI

                                   
section

/-! Actual roster edits, including the noncoverage credit. The fixed-radius
values are persistent over an insertion, and retirements use the true law. -/
noncomputable section
namespace UniformKServer.TierKeyEdits
open Finset FiniteProbability ShortRoster ChronologicalRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)

abbrev RadiusTape (X : Type) [Fintype X] [MetricSpace X] (N K : ℕ) (r : ℝ) :=
  Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r

def keep (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (τ : TierLifetimes.Tape N) (i : Fin N) : Bool :=
  decide (¬ActualRoster.active (TierSchedule.run r K q c n.val) c r K n i ∨
    (¬ActualRoster.compulsory (TierSchedule.run r K q c n.val) c r K i ∧ τ n i=true))

omit [Fintype X] in
theorem sorted_next (r : ℝ) (K : ℕ) (hK : 2≤K) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (τ : TierLifetimes.Tape N) :
    (TierLifetimes.live r K q c (n.val+1) τ).sort (·≤·)=
      KeyEdits.next ((TierLifetimes.live r K q c n.val τ).sort (·≤·)) (keep r K q c n τ) n := by
  rw [TierLifetimes.live,dite_eq_left n.isLt,ite_eq_left hn]
  rw [ShortRoster.insert_linear]
  rw [SortedRoster.sort_insert_last]
  · unfold KeyEdits.next
    congr 1
    exact SortedRoster.sort_filter _ _
  · intro i hi
    exact TierSchedule.index_lt r K q c n.val i
      ((mem_filter.mp ((TierLifetimes.valid r K hK hq q c n.val).1 τ (mem_filter.mp hi).1)).1)

theorem retirement_eq (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (τ : TierLifetimes.Tape N) (ω : RadiusTape X N K r) (p : X) :
    KeyEdits.retirement (TierKeyProcess.key r K q c n.val τ ω p) (keep r K q c n τ)=
      if TierRetirement.event r K q c n τ ω p then 1 else 0 := by
  cases hk : TierKeyProcess.key r K q c n.val τ ω p with
  | none => simp [KeyEdits.retirement,TierRetirement.event,hk]
  | some i =>
    have hi : i∈TierLifetimes.live r K q c n.val τ :=
      (mem_sort _).mp (TierKeys.key_mem _ _ _ c ω p i hk)
    have he : TierRetirement.event r K q c n τ ω p ↔ keep r K q c n τ i=false := by
      unfold TierRetirement.event
      simp only [hk,Option.some.injEq]
      constructor
      · rintro ⟨j, hij, hj, hret⟩
        subst j
        simpa only [keep, decide_eq_false_iff_not, retained, mem_filter, hi, true_and] using hret
      · intro hkf
        refine ⟨i,rfl,hi,?_⟩
        simpa only [keep, decide_eq_false_iff_not, retained, mem_filter, hi, true_and] using hkf
    simp only [KeyEdits.retirement,he]
    cases keep r K q c n τ i <;> rfl

theorem stationary (r : ℝ) (hr : 0<r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (ω : RadiusTape X N K r) (p : X) {J : Type*}
    (earlier : TierLifetimes.Tape N → Option J) (label : TierLifetimes.Tape N → Fin N → J)
    (later : TierLifetimes.Tape N → J) :
    (TierLifetimes.law K hq).expect (fun τ =>
      KeyEdits.changed (earlier τ) (label τ) (later τ)
        (TierKeyProcess.key r K q c n.val τ ω p) (TierKeyProcess.key r K q c (n.val+1) τ ω p)+
      KeyEdits.uncovered (TierKeyProcess.key r K q c (n.val+1) τ ω p)-
      KeyEdits.uncovered (TierKeyProcess.key r K q c n.val τ ω p)) ≤
      2*(if dist (c n) p≤22*r then 49/(K:ℝ) else 0) := by
  have hm := (TierLifetimes.law K hq).expect_mono _ _ (fun τ =>
    KeyEdits.insertion_stationary ((TierLifetimes.live r K q c n.val τ).sort (·≤·))
      (keep r K q c n τ) (fun i => (ω i).val (c i,p)) n (earlier τ) (label τ) (later τ))
  have he (τ : TierLifetimes.Tape N) :
      (KeyEdits.next ((TierLifetimes.live r K q c n.val τ).sort (·≤·)) (keep r K q c n τ) n).find?
        (fun i => (ω i).val (c i,p))=TierKeyProcess.key r K q c (n.val+1) τ ω p := by
    rw [←sorted_next r K hK hq q c n hn τ]; rfl
  simp_rw [he] at hm
  change _ ≤ (TierLifetimes.law K hq).expect (fun τ => 2*KeyEdits.retirement
    (TierKeyProcess.key r K q c n.val τ ω p) (keep r K q c n τ)) at hm
  simp_rw [retirement_eq] at hm
  rw [Law.expect_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (TierRetirement.probability_bound r hr K hK hq q c n ω p) (by norm_num))

theorem mover (r : ℝ) (hr : 0<r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (ω : RadiusTape X N K r) (p : X) {J : Type*}
    (earlier : TierLifetimes.Tape N → Option J) (label : TierLifetimes.Tape N → Fin N → J)
    (later : TierLifetimes.Tape N → J) :
    (TierLifetimes.law K hq).expect (fun τ =>
      KeyEdits.changed (earlier τ) (label τ) (later τ)
        (TierKeyProcess.key r K q c n.val τ ω p) (TierKeyProcess.key r K q c (n.val+1) τ ω p)-
      KeyEdits.uncovered (TierKeyProcess.key r K q c n.val τ ω p)) ≤
      if dist (c n) p≤22*r then 49/(K:ℝ) else 0 := by
  have hm := (TierLifetimes.law K hq).expect_mono _ _ (fun τ =>
    KeyEdits.insertion_mover ((TierLifetimes.live r K q c n.val τ).sort (·≤·))
      (keep r K q c n τ) (fun i => (ω i).val (c i,p)) n (earlier τ) (label τ) (later τ))
  have he (τ : TierLifetimes.Tape N) :
      (KeyEdits.next ((TierLifetimes.live r K q c n.val τ).sort (·≤·)) (keep r K q c n τ) n).find?
        (fun i => (ω i).val (c i,p))=TierKeyProcess.key r K q c (n.val+1) τ ω p := by
    rw [←sorted_next r K hK hq q c n hn τ]; rfl
  simp_rw [he] at hm
  change _ ≤ (TierLifetimes.law K hq).expect (fun τ => KeyEdits.retirement
    (TierKeyProcess.key r K q c n.val τ ω p) (keep r K q c n τ)) at hm
  simp_rw [retirement_eq] at hm
  exact hm.trans (TierRetirement.probability_bound r hr K hK hq q c n ω p)

end UniformKServer.TierKeyEdits

end


end

end OAI
