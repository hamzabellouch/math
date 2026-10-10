import OAI.Combinatorics.ContingencyTables.Model
import Mathlib.Tactic.SplitIfs

namespace OAI

/-! # A literal one-cell lower-bound reduction

Requiring the selected entry to be at least t is equivalent to subtracting
t from that entry, its incident margins and its capacity. The three guards
are retained explicitly, including for zero margins and structural zeros.
-/

namespace ContingencyTables.BoundedCellShift

open scoped BigOperators

variable {m n : ℕ}

def margin (r : Fin m→ℕ) (i₀ : Fin m) (t : ℕ) (i : Fin m) : ℕ :=
  if i=i₀ then r i-t else r i

def lower (X : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n) (t : ℕ)
    (i : Fin m) (j : Fin n) : ℕ :=
  if i=i₀ ∧ j=j₀ then X i j-t else X i j

def raise (X : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n) (t : ℕ)
    (i : Fin m) (j : Fin n) : ℕ :=
  X i j+if i=i₀ ∧ j=j₀ then t else 0

lemma lower_raise (X : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n) (t : ℕ) :
    lower (raise X i₀ j₀ t) i₀ j₀ t=X := by
  funext i j
  by_cases hi : i=i₀ <;> by_cases hj : j=j₀ <;> simp [lower,raise,hi,hj]

lemma raise_lower (X : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n) (t : ℕ)
    (ht : t≤X i₀ j₀) : raise (lower X i₀ j₀ t) i₀ j₀ t=X := by
  funext i j
  by_cases hi : i=i₀ <;> by_cases hj : j=j₀
  · subst i; subst j
    simpa only [raise,lower,ite_true,true_and,add_zero] using Nat.sub_add_cancel ht
  all_goals simp [lower,raise,hi,hj]

lemma raise_row_sum (X : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n)
    (t : ℕ) (i : Fin m) :
    (∑ j,raise X i₀ j₀ t i j)=(∑ j,X i j)+if i=i₀ then t else 0 := by
  by_cases hi : i=i₀
  · subst i
    simp [raise,Finset.sum_add_distrib]
  · simp [raise,hi]

lemma raise_column_sum (X : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n)
    (t : ℕ) (j : Fin n) :
    (∑ i,raise X i₀ j₀ t i j)=(∑ i,X i j)+if j=j₀ then t else 0 := by
  by_cases hj : j=j₀
  · subst j
    simp [raise,Finset.sum_add_distrib]
  · simp [raise,hj]

lemma lower_margins (X : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (i₀ : Fin m) (j₀ : Fin n) (t : ℕ) (hm : HasMargins X r c)
    (ht : t≤X i₀ j₀) :
    HasMargins (lower X i₀ j₀ t) (margin r i₀ t) (margin c j₀ t) := by
  have he := raise_lower X i₀ j₀ t ht
  constructor
  · intro i
    by_cases hi : i=i₀
    · subst i
      have hs := raise_row_sum (lower X i₀ j₀ t) i₀ j₀ t i₀
      rw [he,hm.1 i₀] at hs
      simp only [ite_true] at hs
      simp only [margin,ite_true]
      omega
    · have hs := raise_row_sum (lower X i₀ j₀ t) i₀ j₀ t i
      rw [he,hm.1 i] at hs
      simpa only [margin,hi,ite_false,Nat.add_zero] using hs.symm
  · intro j
    by_cases hj : j=j₀
    · subst j
      have hs := raise_column_sum (lower X i₀ j₀ t) i₀ j₀ t j₀
      rw [he,hm.2 j₀] at hs
      simp only [ite_true] at hs
      simp only [margin,ite_true]
      omega
    · have hs := raise_column_sum (lower X i₀ j₀ t) i₀ j₀ t j
      rw [he,hm.2 j] at hs
      simpa only [margin,hj,ite_false,Nat.add_zero] using hs.symm

lemma raise_margins (Y : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (i₀ : Fin m) (j₀ : Fin n) (t : ℕ)
    (hr : t≤r i₀) (hc : t≤c j₀)
    (hm : HasMargins Y (margin r i₀ t) (margin c j₀ t)) :
    HasMargins (raise Y i₀ j₀ t) r c := by
  constructor
  · intro i
    rw [raise_row_sum,hm.1 i]
    by_cases hi : i=i₀
    · subst i
      simpa [margin] using Nat.sub_add_cancel hr
    · simp [margin,hi]
  · intro j
    rw [raise_column_sum,hm.2 j]
    by_cases hj : j=j₀
    · subst j
      simpa [margin] using Nat.sub_add_cancel hc
    · simp [margin,hj]

lemma lower_bounds (X b : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n)
    (t : ℕ) (hb : ∀ i j,X i j≤b i j) :
    ∀ i j,lower X i₀ j₀ t i j≤lower b i₀ j₀ t i j := by
  intro i j
  unfold lower
  split_ifs
  · exact Nat.sub_le_sub_right (hb i j) t
  · exact hb i j

lemma raise_bounds (Y b : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n)
    (t : ℕ) (ht : t≤b i₀ j₀)
    (hb : ∀ i j,Y i j≤lower b i₀ j₀ t i j) :
    ∀ i j,raise Y i₀ j₀ t i j≤b i j := by
  intro i j
  have h := hb i j
  by_cases hi : i=i₀ <;> by_cases hj : j=j₀
  · subst i; subst j
    simp only [lower,ite_true,true_and] at h
    simp only [raise,ite_true,true_and]
    omega
  all_goals simpa [raise,lower,hi,hj] using h

theorem feasible_lower_iff (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n) (t : ℕ) :
    (∃ X,HasMargins X r c ∧ (∀ i j,X i j≤b i j) ∧ t≤X i₀ j₀) ↔
      t≤r i₀ ∧ t≤c j₀ ∧ t≤b i₀ j₀ ∧
      ∃ Y,HasMargins Y (margin r i₀ t) (margin c j₀ t) ∧
        ∀ i j,Y i j≤lower b i₀ j₀ t i j := by
  constructor
  · rintro ⟨X,hm,hb,ht⟩
    have hc : X i₀ j₀≤c j₀ := by
      rw [←hm.2 j₀]
      exact Finset.single_le_sum (f := fun i=>X i j₀) (fun _ _=>Nat.zero_le _)
        (Finset.mem_univ i₀)
    exact ⟨ht.trans (entry_le_row hm i₀ j₀),ht.trans hc,ht.trans (hb i₀ j₀),
      lower X i₀ j₀ t,lower_margins X r c i₀ j₀ t hm ht,lower_bounds X b i₀ j₀ t hb⟩
  · rintro ⟨hr,hc,hb,Y,hm,hy⟩
    refine ⟨raise Y i₀ j₀ t,raise_margins Y r c i₀ j₀ t hr hc hm,
      raise_bounds Y b i₀ j₀ t hb hy,?_⟩
    simp only [raise,ite_true,true_and]
    omega

end ContingencyTables.BoundedCellShift

end OAI
