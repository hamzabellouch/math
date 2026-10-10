import Mathlib

namespace OAI

noncomputable section

namespace Foulkes.Strips
open Finset Matrix

def incidence {n : ℕ} (S : Fin n → Finset (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  fun r c => if c ∈ S r then 1 else 0

def Laminar {n : ℕ} (S : Fin n → Finset (Fin n)) : Prop :=
  ∀ r s, S r ⊆ S s ∨ S s ⊆ S r ∨ Disjoint (S r) (S s)

theorem incidence_det_bound (n : ℕ) (S : Fin n → Finset (Fin n)) (hS : Laminar S) :
    Int.natAbs (incidence S).det ≤ 1 := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hd : (incidence S).det = 0
    · simp [hd]
    have hnon (r : Fin (n+1)) : (S r).Nonempty := by
      by_contra h
      have he : S r = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      apply hd
      apply Matrix.det_eq_zero_of_row_eq_zero r
      intro c
      simp [incidence, he]
    obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image univ (fun r : Fin (n+1) => (S r).card)
      (Finset.univ_nonempty)
    have hcols {j k : Fin (n+1)} (hj : j ∈ S r) (hk : k ∈ S r) : j = k := by
      by_contra hjk
      apply hd
      apply Matrix.det_zero_of_column_eq hjk
      intro s
      rcases hS r s with hrs | hsr | hdj
      · simp [incidence, hrs hj, hrs hk]
      · have he : S s = S r := Finset.eq_of_subset_of_card_le hsr (hmin s (mem_univ s))
        simp [incidence, he, hj, hk]
      · have hj' : j ∉ S s := fun hs => Finset.disjoint_left.mp hdj hj hs
        have hk' : k ∉ S s := fun hs => Finset.disjoint_left.mp hdj hk hs
        simp [incidence, hj', hk']
    obtain ⟨c, hc⟩ := hnon r
    have hrow : S r = {c} := by
      ext j
      simp only [mem_singleton]
      exact ⟨fun hj => hcols hj hc, fun h => h ▸ hc⟩
    let S' : Fin n → Finset (Fin n) := fun i => univ.filter fun j => c.succAbove j ∈ S (r.succAbove i)
    have hlam : Laminar S' := by
      intro i j
      rcases hS (r.succAbove i) (r.succAbove j) with hij | hji | hdj
      · left
        intro k hk
        simpa [S'] using hij (by simpa [S'] using hk)
      · right; left
        intro k hk
        simpa [S'] using hji (by simpa [S'] using hk)
      · right; right
        apply Finset.disjoint_left.mpr
        intro k hi hj
        exact Finset.disjoint_left.mp hdj (by simpa [S'] using hi) (by simpa [S'] using hj)
    have hminor : (incidence S).submatrix r.succAbove c.succAbove = incidence S' := by
      ext i j
      simp [incidence, S']
    have he : (incidence S).det = (-1 : ℤ) ^ (r.val+c.val) * (incidence S').det := by
      rw [Matrix.det_succ_row _ r]
      simp only [incidence, hrow, mem_singleton]
      simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' univ c]
      simp only [mem_univ, ite_true, hminor]
    rw [he, Int.natAbs_mul, Int.natAbs_pow]
    simpa using ih S' hlam

def assignments {n : ℕ} (i : ℕ) (l m : Fin n → ℕ) : Fin n → Finset (Fin n) :=
  fun r => univ.filter fun c => m c ≤ l r ∧ m c % i = l r % i

lemma assignments_laminar {n : ℕ} (i : ℕ) (l m : Fin n → ℕ) :
    Laminar (assignments i l m) := by
  intro r s
  by_cases he : l r % i = l s % i
  · rcases le_total (l r) (l s) with hrs | hsr
    · left
      intro c hc
      simp only [assignments, mem_filter, mem_univ, true_and] at hc ⊢
      exact ⟨hc.1.trans hrs, hc.2.trans he⟩
    · right; left
      intro c hc
      simp only [assignments, mem_filter, mem_univ, true_and] at hc ⊢
      exact ⟨hc.1.trans hsr, hc.2.trans he.symm⟩
  · right; right
    apply Finset.disjoint_left.mpr
    intro c hr hs
    simp only [assignments, mem_filter, mem_univ, true_and] at hr hs
    exact he (hr.2.symm.trans hs.2)

theorem assignment_det_bound {n : ℕ} (i : ℕ) (l m : Fin n → ℕ) :
    Int.natAbs (incidence (assignments i l m)).det ≤ 1 :=
  incidence_det_bound n _ (assignments_laminar i l m)

end Foulkes.Strips

end

end OAI
