import Mathlib

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def IsRetainedSuffix (A D : Finset ℕ) : Prop :=
  D ⊆ A ∧ ∀ ⦃i j : ℕ⦄, i ∈ D → j ∈ A → i ≤ j → j ∈ D

theorem retainedSuffix_empty_of_last {A D : Finset ℕ} {j : ℕ}
    (hD : IsRetainedSuffix A D) (hA : ∀ i ∈ A,i ≤ j) (hj : j ∈ A) (hcompat : j ∉ D) :
    D=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact hcompat (hD.2 hi hj (hA i (hD.1 hi)))

theorem retainedSuffix_preserves_before_block {A D : Finset ℕ} {s B H : ℕ}
    (hD : IsRetainedSuffix A D) (hcard : D.card ≤ H) (hHB : H < B)
    (hblock : Finset.Ico s (s+B) ⊆ A) {i : ℕ} (hi : i ∈ A) (his : i ≤ s) :
    i ∈ A\D := by
  refine Finset.mem_sdiff.mpr ⟨hi,?_⟩
  intro hid
  have hsub : Finset.Ico s (s+B) ⊆ D := by
    intro k hk
    exact hD.2 hid (hblock hk) (his.trans (Finset.mem_Ico.mp hk).1)
  have h := Finset.card_le_card hsub
  rw [Nat.card_Ico] at h
  omega

theorem protected_block_markers (B H p : ℕ) (hB : 0 < B) (hHB : H < B)
    (A D : ℕ → Finset ℕ)
    (hzero : A 0=∅)
    (hstep : ∀ j < p,A (j+1)=insert j (A j\D j))
    (hrange : ∀ j ≤ p,∀ i ∈ A j,i < j)
    (hsuffix : ∀ j < p,IsRetainedSuffix (A j) (D j))
    (hcard : ∀ j < p,(D j).card ≤ H)
    (hcompatible : ∀ j < p,j%B≠0 → j-1 ∉ D j) :
    ∀ j ≤ p,
      (∀ i, (j-1)/B*B ≤ i → i < j → i ∈ A j) ∧
      (∀ k,k*B < j → k*B ∈ A j) := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hjp : j < p := by omega
    obtain ⟨hc,hm⟩ := ih (by omega)
    rw [hstep j hjp]
    simp only [Nat.add_sub_cancel]
    have hdecomp : j%B+j/B*B=j := by simpa only [Nat.mul_comm B] using Nat.mod_add_div j B
    have hprevle := Nat.div_mul_le_self (j-1) B
    by_cases hr : j%B=0
    · have hjmul : j/B*B=j := by omega
      have hsurvive (i : ℕ) (hi : i ∈ A j) (hij : i ≤ j-B) : i ∈ A j\D j := by
        by_cases hj0 : j=0
        · subst j
          rw [hzero] at hi
          exact False.elim (Finset.notMem_empty i hi)
        · have hBj : B ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) (Nat.dvd_of_mod_eq_zero hr)
          have hq : j/B=(j-1)/B+1 := by
            simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using
              (Nat.succ_div_of_dvd (a:=j-1) (b:=B) (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using Nat.dvd_of_mod_eq_zero hr))
          have ht : (j-1)/B*B=j-B := by
            have hx := congrArg (fun z : ℕ => z*B) hq
            simp only [Nat.add_mul,one_mul] at hx
            omega
          have hb : Finset.Ico (j-B) (j-B+B) ⊆ A j := by
            intro k hk
            have hkj := Finset.mem_Ico.mp hk
            exact hc k (by omega) (by omega)
          exact retainedSuffix_preserves_before_block (hsuffix j hjp) (hcard j hjp) hHB hb hi hij
      constructor
      · intro i hil hij
        have : i=j := by omega
        subst i
        exact Finset.mem_insert_self _ _
      · intro k hk
        by_cases hkj : k*B=j
        · rw [hkj]; exact Finset.mem_insert_self _ _
        · apply Finset.mem_insert_of_mem
          apply hsurvive _ (hm k (by omega))
          have hkj : k < j/B := (Nat.mul_lt_mul_right hB).mp (by omega)
          have hx := Nat.mul_le_mul_right B (show k+1 ≤ j/B by omega)
          simp only [Nat.add_mul,one_mul] at hx
          omega
    · have hj0 : 0 < j := by
        by_contra h
        have hjz : j=0 := by omega
        subst j
        exact hr (by simp)
      have hq : j/B=(j-1)/B := by
        simpa only [Nat.sub_add_cancel hj0] using
          (Nat.succ_div_of_not_dvd (a:=j-1) (b:=B) (by
            simpa only [Nat.sub_add_cancel hj0] using
              (fun h => hr (Nat.mod_eq_zero_of_dvd h))))
      have hqmul := congrArg (fun z : ℕ => z*B) hq
      have hjlast : j-1 ∈ A j := hc (j-1) (by omega) (by omega)
      have hD0 := retainedSuffix_empty_of_last (hsuffix j hjp)
        (fun i hi => by have := hrange j (by omega) i hi; omega) hjlast
        (hcompatible j hjp hr)
      rw [hD0,Finset.sdiff_empty]
      constructor
      · intro i hil hij
        by_cases he : i=j
        · rw [he]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hc i (by omega) (by omega))
      · intro k hk
        by_cases he : k*B=j
        · rw [he]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hm k (by omega))

end SK.Analytic

end
end

end OAI
