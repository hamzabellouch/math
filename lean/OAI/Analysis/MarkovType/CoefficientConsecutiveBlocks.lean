import OAI.Analysis.MarkovType.CoefficientSequenceOps
import Mathlib.Algebra.Module.BigOperators

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n m : ℕ}

def consecutiveBlocks (x : Fin n → E) (cuts : Fin (m + 1) → ℕ) (j : Fin m) : E :=
  ∑ i : Fin n, if cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ then x i else 0

theorem sum_smul_consecutiveBlocks (x : Fin n → E) (cuts : Fin (m + 1) → ℕ)
    (a : Fin m → ℝ) :
    (∑ j : Fin m, a j • consecutiveBlocks x cuts j) =
      ∑ i : Fin n, (∑ j : Fin m,
        if cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ then a j else 0) • x i := by
  simp only [consecutiveBlocks, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [ite_smul, zero_smul]

theorem consecutiveBlocks_cut_iff (cuts : Fin (m + 1) → ℕ)
    (hcuts : Monotone cuts) (j : Fin m) (r : ℕ) (hr : r ≤ m) (i : Fin n)
    (hij : cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ) :
    i.val < cuts ⟨r, Nat.lt_succ_of_le hr⟩ ↔ j.val < r := by
  constructor
  · intro hi
    by_contra hj
    have hc : cuts ⟨r, Nat.lt_succ_of_le hr⟩ ≤ cuts j.castSucc := by
      apply hcuts
      change r ≤ j.val
      exact Nat.le_of_not_gt hj
    omega
  · intro hj
    have hc : cuts j.succ ≤ cuts ⟨r, Nat.lt_succ_of_le hr⟩ := by
      apply hcuts
      change j.val + 1 ≤ r
      exact Nat.succ_le_of_lt hj
    exact hij.2.trans_le hc

theorem sum_prefix_smul_consecutiveBlocks (x : Fin n → E)
    (cuts : Fin (m + 1) → ℕ) (hcuts : Monotone cuts)
    (a : Fin m → ℝ) (r : ℕ) (hr : r ≤ m) :
    (∑ j : Fin m, if j.val < r then a j • consecutiveBlocks x cuts j else 0) =
      ∑ i : Fin n, if i.val < cuts ⟨r, Nat.lt_succ_of_le hr⟩ then
        (∑ j : Fin m,
          if cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ then a j else 0) • x i
        else 0 := by
  have hcoeff (i : Fin n) :
      (∑ j : Fin m, if cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ then
        (if j.val < r then a j else 0) else 0) =
      if i.val < cuts ⟨r, Nat.lt_succ_of_le hr⟩ then
        (∑ j : Fin m, if cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ then a j else 0)
      else 0 := by
    by_cases hi : i.val < cuts ⟨r, Nat.lt_succ_of_le hr⟩
    · rw [ite_eq_left hi]
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hij : cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ
      · have hj := (consecutiveBlocks_cut_iff cuts hcuts j r hr i hij).mp hi
        simp only [ite_eq_left hij, ite_eq_left hj]
      · simp only [ite_eq_right hij]
    · rw [ite_eq_right hi]
      apply Finset.sum_eq_zero
      intro j _hj
      by_cases hij : cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ
      · have hj : ¬ j.val < r :=
          fun hj => hi ((consecutiveBlocks_cut_iff cuts hcuts j r hr i hij).mpr hj)
        simp only [ite_eq_left hij, ite_eq_right hj]
      · simp only [ite_eq_right hij]
  have h := sum_smul_consecutiveBlocks x cuts (fun j => if j.val < r then a j else 0)
  simp only [ite_smul, zero_smul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hcoeff]
  simp only [ite_smul, zero_smul]

theorem CoefficientBasic.consecutiveBlocks {K : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (cuts : Fin (m + 1) → ℕ)
    (hcuts : Monotone cuts) (hlast : cuts (Fin.last m) ≤ n) :
    CoefficientBasic K (consecutiveBlocks x cuts) := by
  intro a r hr
  rw [sum_prefix_smul_consecutiveBlocks x cuts hcuts a r hr,
    sum_smul_consecutiveBlocks]
  apply hx
  exact (hcuts (show (⟨r, Nat.lt_succ_of_le hr⟩ : Fin (m + 1)) ≤ Fin.last m from hr)).trans hlast

end MarkovSuperreflexivity

end OAI
