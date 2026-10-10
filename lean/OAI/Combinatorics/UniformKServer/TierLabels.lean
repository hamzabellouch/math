import Mathlib
import OAI.Combinatorics.UniformKServer.TierLifetimes
import OAI.Combinatorics.UniformKServer.CooldownLabels

namespace OAI

                                 
section

/-! Actual horizon/law independent pool sizes; labels remain reserved after a
record retires or becomes shadowed. All births are chronological identities. -/
noncomputable section
namespace UniformKServer.TierLabels
open Finset ChronologicalRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

def reserved (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) : Finset (Fin N) :=
  young (TierSchedule.run r K q c t) c r (K^2)

def birth (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) : Option (Fin N) :=
  if ht : t<N then
    if TierSchedule.trigger r K (TierSchedule.run r K q c t) q c ⟨t,ht⟩ then some ⟨t,ht⟩ else none
  else none

theorem reserved_card (r : ℝ) (hr : 0≤r) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) :
    (reserved r K q c t).card≤Fintype.card X*K^2 := global_young_count _ c r hr _

omit [Fintype X] in
theorem reserved_zero (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) :
    reserved r K q c 0=∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  exact notMem_empty i (mem_filter.mp hi).1

omit [Fintype X] in
theorem reserved_next (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) :
    reserved r K q c (t+1)⊆match birth r K q c t with
      | none => reserved r K q c t
      | some n => insert n (reserved r K q c t) := by
  by_cases ht : t<N
  · let n : Fin N := ⟨t,ht⟩
    by_cases hn : TierSchedule.trigger r K (TierSchedule.run r K q c t) q c n
    · have hb : birth r K q c t=some n := by rw [birth,dite_eq_left ht,ite_eq_left hn]
      rw [hb]
      have hy := TierSchedule.young_next_subset r K (K^2) q c n
      intro i hi
      rcases mem_insert.mp (hy hi) with h|h
      · exact mem_insert.mpr (Or.inl h)
      · exact mem_insert_of_mem h
    · have hb : birth r K q c t=none := by rw [birth,dite_eq_left ht,ite_eq_right hn]
      have hr : TierSchedule.run r K q c (t+1)=TierSchedule.run r K q c t := by
        rw [TierSchedule.run,dite_eq_left ht,ite_eq_right hn]
      rw [hb]
      exact le_of_eq (congrArg (fun s => young s c r (K^2)) hr)
  · have hb : birth r K q c t=none := by rw [birth,dite_eq_right ht]
    have hr : TierSchedule.run r K q c (t+1)=TierSchedule.run r K q c t := by
      rw [TierSchedule.run,dite_eq_right ht]
    rw [hb]
    exact le_of_eq (congrArg (fun s => young s c r (K^2)) hr)

omit [Fintype X] in
theorem birth_new (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) (n : Fin N)
    (hb : birth r K q c t=some n) : n∉reserved r K q c t := by
  have hn : n.val=t := by
    unfold birth at hb
    split_ifs at hb with ht hn
    · exact congrArg Fin.val (Option.some.inj hb).symm
  intro hi
  have hlt := TierSchedule.index_lt r K q c t n ((mem_filter.mp hi).1)
  omega

def labels (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) :=
  CooldownLabels.run (Fintype.card X*K^2) (reserved r K q c) (birth r K q c) t

theorem injective (r : ℝ) (hr : 0≤r) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) :
    Set.InjOn (labels r K q c t).label (reserved r K q c t) :=
  CooldownLabels.injective (Fintype.card X*K^2) (reserved r K q c) (birth r K q c) (reserved_card r hr K q c) (reserved_zero r K q c)
    (fun t => by
      cases hb : birth r K q c t <;> simpa only [hb] using reserved_next r K q c t)
    (birth_new r K q c) t

theorem common_record (r : ℝ) (hr : 0≤r) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (i j : Fin N) (hi : i∈reserved r K q c t) (hj : j∈reserved r K q c (t+1))
    (he : (labels r K q c t).label i=(labels r K q c (t+1)).label j) : i=j :=
  CooldownLabels.common_anchor (Fintype.card X*K^2) (reserved r K q c) (birth r K q c) (reserved_card r hr K q c) (reserved_zero r K q c)
    (fun t => by
      cases hb : birth r K q c t <;> simpa only [hb] using reserved_next r K q c t)
    (birth_new r K q c) t i j hi hj he

omit [Fintype X] in
theorem live_reserved (r : ℝ) (K : ℕ) (hK : 2≤K) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) (τ : TierLifetimes.Tape N) :
    TierLifetimes.live r K q c t τ ⊆ reserved r K q c t :=
  (TierLifetimes.valid r K hK hq q c t).1 τ

end UniformKServer.TierLabels

end


end

end OAI
