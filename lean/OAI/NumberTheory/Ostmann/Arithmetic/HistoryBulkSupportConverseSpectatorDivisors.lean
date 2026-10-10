import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSkeleton
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesPrecision

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistorySignedResidues HistoryOccurrenceVariables

theorem NodeStatic.compensation_product_pos {l : ℕ} {a : State}
    {u hp hm : List SmallSlot} {left right : History l}
    (hs : NodeStatic a u hp hm left right) : 0<(u.map SmallSlot.value).prod := by
  apply List.prod_pos
  intro q hq
  obtain ⟨slot,hslot,rfl⟩ := List.mem_map.mp hq
  exact (hs.primeComp slot hslot).pos

theorem divisorProduct_ne_zero_of_static {l : ℕ} (h : History l) {V : ℕ→ℕ}
    (hs : StaticSkeleton V h) : divisorProduct h≠0 := by
  induction h with
  | leaf a => exact one_ne_zero
  | node a p u hp hm left right il ir =>
    have hu : ((u.map SmallSlot.value).prod:ℤ)≠0 := by
      exact_mod_cast hs.2.1.compensation_product_pos.ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hs.1.frequency_ne_zero hu)
      (il hs.2.2.1)) (ir hs.2.2.2)

theorem divisorData_of_static {l : ℕ} (h : History l) {V : ℕ→ℕ}
    (hs : StaticSkeleton V h) : DivisorData (divisorProduct h) h := by
  induction h with
  | leaf a => trivial
  | node a p u hp hm left right il ir =>
    have hu : ((u.map SmallSlot.value).prod:ℤ)≠0 := by
      exact_mod_cast hs.2.1.compensation_product_pos.ne'
    refine ⟨mul_ne_zero hs.1.frequency_ne_zero hu,?_,?_,?_⟩
    · change _ ∣ (_*divisorProduct left)*divisorProduct right
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · apply (il hs.2.2.1).mono
      exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    · apply (ir hs.2.2.2).mono
      exact dvd_mul_left _ _

theorem divisorProduct_coprime_of_frequencies_internal {l : ℕ} (h : History l) (N : ℕ)
    (hf : ∀s∈h.frequencies,Nat.Coprime s.natAbs N)
    (hi : ∀i:InternalKey h,Nat.Coprime (internalSlot h i).value N) :
    Nat.Coprime (divisorProduct h).natAbs N := by
  induction h with
  | leaf a => simp [divisorProduct]
  | node a p u hp hm left right il ir =>
    have hu : Nat.Coprime (u.map SmallSlot.value).prod N := by
      apply Nat.coprime_list_prod_left_iff.mpr
      intro q hq
      obtain ⟨slot,hslot,rfl⟩ := List.mem_map.mp hq
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hslot
      exact hi (.inl i)
    have ha := hf a.frequency (by simp [History.frequencies])
    have hl := il
      (fun s hmem => hf s (by
        simp only [History.frequencies,List.mem_cons,List.mem_append]
        exact Or.inr (Or.inl hmem)))
      (fun i => hi (.inr (.inl i)))
    have hr := ir
      (fun s hmem => hf s (by
        simp only [History.frequencies,List.mem_cons,List.mem_append]
        exact Or.inr (Or.inr hmem)))
      (fun i => hi (.inr (.inr i)))
    simpa only [divisorProduct,Int.natAbs_mul,Int.natAbs_natCast] using
      ((ha.mul_left hu).mul_left hl).mul_left hr

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
