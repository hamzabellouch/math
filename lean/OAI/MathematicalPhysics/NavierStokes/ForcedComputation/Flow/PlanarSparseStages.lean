import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

namespace OAI

/-! Embedding a branch's local stages into the complete pulse schedule.
The anchor changes exactly at a selected pulse and remains fixed in all
other slots. -/

namespace ForcedComputation.PlanarRouting
open Finset

def stagesBefore {m n : ℕ} (J : Fin m → Fin n) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun k => (J k).val < i)).card

theorem stagesBefore_le {m n : ℕ} (J : Fin m → Fin n) (i : ℕ) :
    stagesBefore J i ≤ m := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun k : Fin m => (J k).val < i) Finset.univ)
  simpa only [stagesBefore, Finset.card_univ, Fintype.card_fin] using h

@[simp] theorem stagesBefore_zero {m n : ℕ} (J : Fin m → Fin n) :
    stagesBefore J 0 = 0 := by simp [stagesBefore]

@[simp] theorem stagesBefore_last {m n : ℕ} (J : Fin m → Fin n) :
    stagesBefore J n = m := by
  have he : Finset.univ.filter (fun k : Fin m => (J k).val < n) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro k _
    exact (J k).isLt
  simp only [stagesBefore, he, Finset.card_univ, Fintype.card_fin]

theorem stagesBefore_selected {m n : ℕ} {J : Fin m → Fin n} (hJ : StrictMono J)
    (k : Fin m) : stagesBefore J (J k).val = k.val := by
  have he : Finset.univ.filter (fun l : Fin m => (J l).val < (J k).val) =
      Finset.Iio k := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact hJ.lt_iff_lt
  rw [stagesBefore, he, Fin.card_Iio]

theorem stagesBefore_selected_succ {m n : ℕ} {J : Fin m → Fin n}
    (hJ : StrictMono J) (k : Fin m) : stagesBefore J ((J k).val + 1) = k.val + 1 := by
  have he : Finset.univ.filter (fun l : Fin m => (J l).val < (J k).val + 1) =
      Finset.Iic k := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    change (J l).val < (J k).val + 1 ↔ l ≤ k
    rw [Nat.lt_succ_iff]
    exact hJ.le_iff_le
  rw [stagesBefore, he, Fin.card_Iic]

theorem stagesBefore_unused {m n : ℕ} (J : Fin m → Fin n) (i : ℕ)
    (hi : ∀ k, (J k).val ≠ i) : stagesBefore J (i + 1) = stagesBefore J i := by
  unfold stagesBefore
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hk := hi k
  omega

def sparseAnchor {E : Type*} {m n : ℕ} (J : Fin m → Fin n)
    (p : Fin (m + 1) → E) (i : ℕ) : E :=
  p ⟨stagesBefore J i, lt_of_le_of_lt (stagesBefore_le J i) (Nat.lt_succ_self m)⟩

@[simp] theorem sparseAnchor_zero {E : Type*} {m n : ℕ} (J : Fin m → Fin n)
    (p : Fin (m + 1) → E) : sparseAnchor J p 0 = p 0 := by
  unfold sparseAnchor
  apply congrArg p
  apply Fin.ext
  exact stagesBefore_zero J

@[simp] theorem sparseAnchor_last {E : Type*} {m n : ℕ} (J : Fin m → Fin n)
    (p : Fin (m + 1) → E) : sparseAnchor J p n = p (Fin.last m) := by
  unfold sparseAnchor
  apply congrArg p
  apply Fin.ext
  exact stagesBefore_last J

theorem sparseAnchor_after_last {E : Type*} {m n : ℕ} (J : Fin m → Fin n)
    (p : Fin (m + 1) → E) {i : ℕ} (hi : n ≤ i) :
    sparseAnchor J p i = p (Fin.last m) := by
  have he : Finset.univ.filter (fun k : Fin m => (J k).val < i) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro k _
    exact (J k).isLt.trans_le hi
  unfold sparseAnchor
  apply congrArg p
  apply Fin.ext
  simp only [stagesBefore, he, Finset.card_univ, Fintype.card_fin, Fin.val_last]

theorem sparseAnchor_selected {E : Type*} {m n : ℕ} {J : Fin m → Fin n}
    (hJ : StrictMono J) (p : Fin (m + 1) → E) (k : Fin m) :
    sparseAnchor J p (J k).val = p k.castSucc := by
  unfold sparseAnchor
  apply congrArg p
  apply Fin.ext
  exact stagesBefore_selected hJ k

theorem sparseAnchor_selected_succ {E : Type*} {m n : ℕ} {J : Fin m → Fin n}
    (hJ : StrictMono J) (p : Fin (m + 1) → E) (k : Fin m) :
    sparseAnchor J p ((J k).val + 1) = p k.succ := by
  unfold sparseAnchor
  apply congrArg p
  apply Fin.ext
  exact stagesBefore_selected_succ hJ k

theorem sparseAnchor_unused {E : Type*} {m n : ℕ} (J : Fin m → Fin n)
    (p : Fin (m + 1) → E) (i : ℕ) (hi : ∀ k, (J k).val ≠ i) :
    sparseAnchor J p (i + 1) = sparseAnchor J p i := by
  unfold sparseAnchor
  apply congrArg p
  apply Fin.ext
  exact stagesBefore_unused J i hi

end ForcedComputation.PlanarRouting

end OAI
