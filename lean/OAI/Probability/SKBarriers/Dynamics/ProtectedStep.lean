import Mathlib
import OAI.Probability.SKBarriers.Dynamics.ProtectedBlock

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

def BlockProtected (B j : ℕ) (A : Finset ℕ) : Prop :=
  (∀ i,(j-1)/B*B ≤ i → i < j → i ∈ A) ∧ (∀ k, k*B < j → k*B ∈ A)

theorem protected_block_step (B H j : ℕ) (hB : 0 < B) (hHB : H < B)
    (A D : Finset ℕ) (hA : ∀ i ∈ A, i < j) (hc : BlockProtected B j A)
    (hs : IsRetainedSuffix A D) (hcard : D.card ≤ H)
    (hcompat : j%B ≠ 0 → j-1∉D) :
    BlockProtected B (j+1) (insert j (A\D)) ∧ (0 < j → 0 ∈ A\D) := by
  classical
  obtain ⟨hc,hm⟩ := hc
  have hdecomp : j%B+j/B*B=j := by simpa only [Nat.mul_comm B] using Nat.mod_add_div j B
  have hprevle := Nat.div_mul_le_self (j-1) B
  by_cases hr : j%B=0
  · have hjmul : j/B*B=j := by omega
    have hsurvive (i : ℕ) (hi : i ∈ A) (hij : i ≤ j-B) : i ∈ A\D := by
      have hj0 : 0 < j := by have := hA i hi; omega
      have hBj : B ≤ j := Nat.le_of_dvd hj0 (Nat.dvd_of_mod_eq_zero hr)
      have hq : j/B=(j-1)/B+1 := by
        simpa only [Nat.sub_add_cancel hj0] using
          (Nat.succ_div_of_dvd (a:=j-1) (b:=B) (by simpa only [Nat.sub_add_cancel hj0] using Nat.dvd_of_mod_eq_zero hr))
      have ht : (j-1)/B*B=j-B := by
        have hx := congrArg (fun z : ℕ => z*B) hq
        simp only [Nat.add_mul,one_mul] at hx
        omega
      have hb : Finset.Ico (j-B) (j-B+B) ⊆ A := by
        intro k hk
        have hkj := Finset.mem_Ico.mp hk
        exact hc k (by omega) (by omega)
      exact retainedSuffix_preserves_before_block hs hcard hHB hb hi hij
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i hil hij
      simp only [Nat.add_sub_cancel] at hil
      have : i=j := by omega
      subst i
      exact Finset.mem_insert_self _ _
    · intro k hk
      by_cases he : k*B=j
      · rw [he]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply hsurvive _ (hm k (by omega))
        have hlt : k < j/B := (Nat.mul_lt_mul_right hB).mp (by omega)
        have hx := Nat.mul_le_mul_right B (show k+1 ≤ j/B by omega)
        simp only [Nat.add_mul,one_mul] at hx
        omega
    · intro hj
      apply hsurvive 0
      · simpa using hm 0 (by simpa using hj)
      · omega
  · have hj0 : 0 < j := by
      by_contra h
      have hjz : j=0 := by omega
      subst j
      exact hr (by simp)
    have hq : j/B=(j-1)/B := by
      simpa only [Nat.sub_add_cancel hj0] using
        (Nat.succ_div_of_not_dvd (a:=j-1) (b:=B) (by
          simpa only [Nat.sub_add_cancel hj0] using (fun h => hr (Nat.mod_eq_zero_of_dvd h))))
    have hqmul := congrArg (fun z : ℕ => z*B) hq
    have hjlast : j-1 ∈ A := hc (j-1) (by omega) (by omega)
    have hD0 := retainedSuffix_empty_of_last hs (fun i hi => by have := hA i hi; omega) hjlast (hcompat hr)
    rw [hD0,Finset.sdiff_empty]
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i hil hij
      simp only [Nat.add_sub_cancel] at hil
      by_cases he : i=j
      · rw [he]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hc i (by omega) (by omega))
    · intro k hk
      by_cases he : k*B=j
      · rw [he]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hm k (by omega))
    · intro _
      simpa using hm 0 (by simpa using hj0)

end SK.Analytic

end
end

end OAI
