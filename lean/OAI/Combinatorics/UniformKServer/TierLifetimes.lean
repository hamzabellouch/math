import Mathlib
import OAI.Combinatorics.UniformKServer.TierSchedule
import OAI.Combinatorics.UniformKServer.ActualRoster
import OAI.Combinatorics.UniformKServer.PiFresh

namespace OAI

                                    
section

/-! Actual tier lifetimes on one fixed finite independent tape. The chronological
schedule is formed before this tape and is not redefined by realized survival. -/
noncomputable section
namespace UniformKServer.TierLifetimes
open Finset FiniteProbability ChronologicalRoster ShortRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [MetricSpace X] {N : ℕ}
local instance indexDecEq : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)

abbrev Tape (N : ℕ) := Fin N → (Fin N → Bool)

def live (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) : ℕ → Tape N → Finset (Fin N)
  | 0, _ => ∅
  | t+1, τ => if ht : t<N then
      let n : Fin N := ⟨t,ht⟩
      let S := TierSchedule.run r K q c t
      if TierSchedule.trigger r K S q c n then
        insert n (retained (ActualRoster.active S c r K n) (ActualRoster.compulsory S c r K) (live r K q c t τ) (τ n))
      else live r K q c t τ
    else live r K q c t τ

theorem live_congr (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (a b : Tape N) (hab : ∀ j : Fin N, j.val<t → a j=b j) :
    live r K q c t a=live r K q c t b := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun j hj => hab j (Nat.lt_succ_of_lt hj))
    simp only [live]
    split_ifs with ht hn
    · rw [he,hab ⟨t,ht⟩ (Nat.lt_succ_self t)]
    · exact he
    · exact he

def law (K : ℕ) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) : Law (Tape N) :=
  Law.pi (I:=Fin N) (A:=fun _ => Fin N → Bool) (fun _ => fresh (I:=Fin N) (1/(K:ℝ)) hq)

def state (r : ℝ) (K : ℕ) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) : State (Fin N) where
  Sample := Tape N
  finite := inferInstance
  law := law K hq
  live := live r K q c t

theorem fresh_step (r : ℝ) (K : ℕ) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (g : Finset (Fin N) → (Fin N → Bool) → ℝ) :
    (law K hq).expect (fun τ => g (live r K q c n.val τ) (τ n))=
      ((law K hq).prod (fresh (1/(K:ℝ)) hq)).expect (fun z => g (live r K q c n.val z.1) z.2) := by
  apply Law.expect_pi_fresh
  intro a b he
  apply live_congr
  intro j hj
  exact he j (fun h => by subst j; omega)

theorem valid (r : ℝ) (K : ℕ) (hK : 2≤K) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) :
    ActualRoster.valid (state r K hq q c t) (TierSchedule.run r K q c t) c r K := by
  induction t with
  | zero =>
    constructor
    · intro τ; exact empty_subset _
    · intro i
      change (law K hq).expect (fun _ => if i∈(∅ : Finset (Fin N)) then 1 else 0)=_
      simp only [notMem_empty,ite_false,Law.expect_const,TierSchedule.run]
  | succ t ih =>
    by_cases ht : t<N
    · let n : Fin N := ⟨t,ht⟩
      let S := TierSchedule.run r K q c t
      by_cases hn : TierSchedule.trigger r K S q c n
      · have hv := ActualRoster.next_valid (state r K hq q c t) S c r K hK hq n ih
          (fun i hi => TierSchedule.index_lt r K q c t i hi)
        have hr : TierSchedule.run r K q c (t+1)=insert n S := by
          rw [TierSchedule.run,dite_eq_left ht,ite_eq_left hn]
          ext i
          simp only [mem_insert]
          rfl
        have hl (τ : Tape N) : live r K q c (t+1) τ=
            (ActualRoster.next (state r K hq q c t) S c r K hq n).live (τ,τ n) := by
          rw [live,dite_eq_left ht]
          change (if TierSchedule.trigger r K S q c n then _ else _)=_
          rw [ite_eq_left hn]
          ext i
          simp only [ActualRoster.next,state,mem_insert]
          rfl
        rw [hr]
        constructor
        · change ∀ τ : Tape N, live r K q c (t+1) τ ⊆ _
          intro τ
          rw [hl]
          exact hv.1 (τ,τ n)
        · intro i
          change (law K hq).expect (fun τ => if i∈live r K q c (t+1) τ then 1 else 0)=_
          simp_rw [hl]
          change (law K hq).expect (fun τ => if i∈insert n
            (retained (ActualRoster.active S c r K n) (ActualRoster.compulsory S c r K) (live r K q c n.val τ) (τ n)) then 1 else 0)=_
          rw [fresh_step r K hq q c n (fun H τ => if i∈insert n
            (retained (ActualRoster.active S c r K n) (ActualRoster.compulsory S c r K) H τ) then 1 else 0)]
          exact hv.2 i
      · have hr : TierSchedule.run r K q c (t+1)=S := by
          rw [TierSchedule.run,dite_eq_left ht,ite_eq_right hn]
        have hl : state r K hq q c (t+1)=state r K hq q c t := by
          unfold state
          congr 1
          funext τ
          rw [live,dite_eq_left ht]
          change (if TierSchedule.trigger r K S q c n then _ else _)=_
          rw [ite_eq_right hn]
        rw [hr,hl]; exact ih
    · have hr : TierSchedule.run r K q c (t+1)=TierSchedule.run r K q c t := by
        rw [TierSchedule.run,dite_eq_right ht]
      have hl : state r K hq q c (t+1)=state r K hq q c t := by
        unfold state
        congr 1
        funext τ
        simp only [live,dite_eq_right ht]
      rw [hr,hl]; exact ih

theorem young_present (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (τ : Tape N) :
    young (TierSchedule.run r K q c t) c r K ⊆ live r K q c t τ := by
  induction t with
  | zero => intro i hi; exact (notMem_empty i (mem_filter.mp hi).1).elim
  | succ t ih =>
    by_cases ht : t<N
    · let n : Fin N := ⟨t,ht⟩
      let S := TierSchedule.run r K q c t
      by_cases hn : TierSchedule.trigger r K S q c n
      · have hr : TierSchedule.run r K q c (t+1)=insert n S := by
          rw [TierSchedule.run,dite_eq_left ht,ite_eq_left hn]
          ext i; simp only [mem_insert]; rfl
        rw [hr,live,dite_eq_left ht]
        change young (insert n S) c r K ⊆
          (if TierSchedule.trigger r K S q c n then _ else _)
        rw [ite_eq_left hn]
        intro i hi
        rcases mem_filter.mp hi with ⟨hi,hage⟩
        rcases mem_insert.mp hi with hnew|hi
        · exact mem_insert.mpr (Or.inl hnew)
        · apply mem_insert_of_mem
          apply mem_filter.mpr
          have horder : ∀ j ∈ S, j<n := fun j hj => TierSchedule.index_lt r K q c t j hj
          rw [ShortRoster.insert_linear S n,age_insert S c r n i horder hi] at hage
          have hold : age S c r i<K := by split_ifs at hage <;> omega
          refine ⟨ih (mem_filter.mpr ⟨hi,hold⟩),Or.inl ?_⟩
          intro ha
          have hd := ha.1
          rw [ite_eq_left hd] at hage
          exact (not_le_of_gt hage) ha.2
      · have hr : TierSchedule.run r K q c (t+1)=S := by
          rw [TierSchedule.run,dite_eq_left ht,ite_eq_right hn]
        rw [hr,live,dite_eq_left ht]
        change young S c r K ⊆ (if TierSchedule.trigger r K S q c n then _ else _)
        rw [ite_eq_right hn]
        exact ih
    · simpa only [TierSchedule.run,live,dite_eq_right ht] using ih

theorem coverage (r : ℝ) (hr : 0≤r) (K : ℕ) (hK : 0<K)
    (q : Fin N → Prop) (c : Fin N → X) (n : Fin N) (hn : q n) (τ : Tape N) :
    ∃ i∈live r K q c (n.val+1) τ, dist (c n) (c i)≤r/2 := by
  obtain ⟨i,hi,hd⟩ := TierSchedule.chronological_coverage r hr K hK q c n hn
  exact ⟨i,young_present r K q c _ τ hi,hd⟩

end UniformKServer.TierLifetimes

end


end

end OAI
