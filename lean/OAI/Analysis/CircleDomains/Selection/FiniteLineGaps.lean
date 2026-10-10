import Mathlib.Order.Interval.Finset.Gaps
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace OAI

/-!
# The actual gaps of finitely many disjoint line intervals

Sorting the closed holes supplies the open intervals on which variation
is paid. Every gap is nonempty, the gaps are disjoint, and no point of a
gap belongs to a hole. Point holes are allowed.
-/

open Set Function

namespace CircleDomainRigidity

noncomputable def gapsAfterHoles {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (i : Fin (n + 1)) : ℝ × ℝ :=
  (Fin.cons (α := fun _ => ℝ) a (fun j => (H j).2) i, Fin.snoc (α := fun _ => ℝ) (fun j => (H j).1) b i)

@[simp] theorem gapsAfterHoles_zero_fst {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ) :
    (gapsAfterHoles a b H 0).1 = a := by simp [gapsAfterHoles]

@[simp] theorem gapsAfterHoles_last_snd {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ) :
    (gapsAfterHoles a b H (Fin.last n)).2 = b := by simp [gapsAfterHoles]

@[simp] theorem gapsAfterHoles_succ_fst {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (i : Fin n) : (gapsAfterHoles a b H i.succ).1 = (H i).2 := by
  simp [gapsAfterHoles]

@[simp] theorem gapsAfterHoles_castSucc_snd {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (i : Fin n) : (gapsAfterHoles a b H i.castSucc).2 = (H i).1 := by
  simp [gapsAfterHoles]

theorem gapsAfterHoles_strict {n : ℕ} {a b : ℝ} (hab : a < b) (H : Fin n → ℝ × ℝ)
    (hinside : ∀ i, a < (H i).1 ∧ (H i).1 ≤ (H i).2 ∧ (H i).2 < b)
    (hsep : ∀ i j, i < j → (H i).2 < (H j).1) (i : Fin (n + 1)) :
    (gapsAfterHoles a b H i).1 < (gapsAfterHoles a b H i).2 := by
  cases n with
  | zero => fin_cases i; simpa [gapsAfterHoles, Fin.snoc] using hab
  | succ n =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change a < Fin.snoc (α := fun _ => ℝ) (fun j => (H j).1) b (0 : Fin (n + 2))
      simpa only [← Fin.castSucc_zero, Fin.snoc_castSucc] using (hinside 0).1
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [gapsAfterHoles_succ_fst, Fin.succ_last, gapsAfterHoles_last_snd]
        exact (hinside (Fin.last n)).2.2
      · rw [gapsAfterHoles_succ_fst, ← Fin.castSucc_succ, gapsAfterHoles_castSucc_snd]
        exact hsep j.castSucc j.succ (by simp)

theorem gapsAfterHoles_avoid {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hfirst : Monotone (fun i => (H i).1)) (hlast : Monotone (fun i => (H i).2))
    (i : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo
      (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2) :
    ∀ j, x ∉ Icc (H j).1 (H j).2 := by
  intro j hj
  by_cases hji : j.val < i.val
  · obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero (show i ≠ 0 by intro he; simp [he] at hji)
    rw [gapsAfterHoles_succ_fst] at hx
    have hjk : j ≤ k := by
      simpa only [Fin.le_iff_val_le_val] using Nat.le_of_lt_succ hji
    exact (not_lt_of_ge (hj.2.trans (hlast hjk))) hx.1
  · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last
      (show i ≠ Fin.last n by intro he; subst i; exact hji j.isLt)
    rw [gapsAfterHoles_castSucc_snd] at hx
    have hkj : k ≤ j := by
      exact Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hji)
    exact (not_lt_of_ge ((hfirst hkj).trans hj.1)) hx.2

theorem gapsAfterHoles_disjoint {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hvalid : ∀ i, (H i).1 ≤ (H i).2)
    (hfirst : Monotone (fun i => (H i).1)) :
    Pairwise (Disjoint on fun i => Ioo
      (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2) := by
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)).symm
  obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last
    (show i ≠ Fin.last n by
      intro he
      subst i
      exact (not_lt_of_ge (Fin.le_last j)) hlt)
  obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero
    (show j ≠ 0 by intro he; simp [he] at hlt)
  have hkl : k ≤ l := by
    exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hlt)
  apply disjoint_left.mpr
  intro x hx hy
  dsimp only at hx hy
  rw [gapsAfterHoles_castSucc_snd] at hx
  rw [gapsAfterHoles_succ_fst] at hy
  exact (not_lt_of_ge (((hfirst hkl).trans (hvalid l)).trans hy.1.le)) hx.2

theorem interval_right_lt_left_of_disjoint {z w : ℝ × ℝ}
    (hw : w.1 ≤ w.2)
    (hfirst : z.1 ≤ w.1) (hdisj : Disjoint (Icc z.1 z.2) (Icc w.1 w.2)) :
    z.2 < w.1 := by
  by_contra h
  exact (disjoint_left.mp hdisj ⟨hfirst, le_of_not_gt h⟩ ⟨le_rfl, hw⟩)

theorem sorted_holes_separated (F : Finset (ℝ × ℝ))
    (hvalid : ∀ z ∈ F, z.1 ≤ z.2)
    (hdisj : (↑F : Set (ℝ × ℝ)).PairwiseDisjoint (fun z => Icc z.1 z.2)) :
    ∀ i j : Fin F.card, i < j →
      (F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl i).2 <
        (F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl j).1 := by
  intro i j hij
  let H := F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl
  have hi := F.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ) rfl i
  have hj := F.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ) rfl j
  exact interval_right_lt_left_of_disjoint (hvalid _ hj)
    (Prod.Lex.le_iff'.mp (H.monotone hij.le)).1
    (hdisj hi hj (H.injective.ne hij.ne))

end CircleDomainRigidity

end OAI
