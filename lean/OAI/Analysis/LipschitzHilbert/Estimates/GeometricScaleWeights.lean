import OAI.Analysis.LipschitzHilbert.Estimates.FiniteEnergySchur
import Mathlib.Data.Nat.Dist

namespace OAI

/-! Uniform row and column bounds for the actual geometric scale kernel. -/

open scoped BigOperators

noncomputable section

namespace LipschitzHilbert

theorem sum_half_powers_le_two (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) ≤ 2 := by
  have heq : (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) =
      2 * (1 - (1 / 2 : ℝ) ^ N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [heq]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N]

theorem sum_half_distance_le_four (N i : ℕ) :
    (∑ j : Fin N, (1 / 2 : ℝ) ^ Nat.dist i j.val) ≤ 4 := by
  classical
  let s := Finset.univ.filter (fun j : Fin N => j.val ≤ i)
  let t := Finset.univ.filter (fun j : Fin N => ¬j.val ≤ i)
  have hs : (∑ j ∈ s, (1 / 2 : ℝ) ^ Nat.dist i j.val) ≤ 2 := by
    have hinj : Set.InjOn (fun j : Fin N => i - j.val) s := by
      intro j hj k hk heq
      have hj' := (Finset.mem_filter.mp hj).2
      have hk' := (Finset.mem_filter.mp hk).2
      change i - j.val = i - k.val at heq
      apply Fin.ext
      omega
    have hmap : s.image (fun j : Fin N => i - j.val) ⊆
        Finset.range (i + N + 1) := by
      intro n hn
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hn
      simp only [Finset.mem_range]
      omega
    have h := Finset.sum_le_sum_of_injOn (fun j : Fin N => i - j.val) hinj hmap
      (s := s) (t := Finset.range (i + N + 1))
      (f := fun j => (1 / 2 : ℝ) ^ Nat.dist i j.val)
      (g := fun n => (1 / 2 : ℝ) ^ n)
      (fun j hj => by rw [Nat.dist_eq_sub_of_le_right (Finset.mem_filter.mp hj).2])
      (fun n _ _ => pow_nonneg (by norm_num) n)
    exact h.trans (sum_half_powers_le_two _)
  have ht : (∑ j ∈ t, (1 / 2 : ℝ) ^ Nat.dist i j.val) ≤ 2 := by
    have hinj : Set.InjOn (fun j : Fin N => j.val - i) t := by
      intro j hj k hk heq
      have hj' := (Finset.mem_filter.mp hj).2
      have hk' := (Finset.mem_filter.mp hk).2
      change j.val - i = k.val - i at heq
      apply Fin.ext
      omega
    have hmap : t.image (fun j : Fin N => j.val - i) ⊆
        Finset.range (i + N + 1) := by
      intro n hn
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hn
      simp only [Finset.mem_range]
      have := j.isLt
      omega
    have h := Finset.sum_le_sum_of_injOn (fun j : Fin N => j.val - i) hinj hmap
      (s := t) (t := Finset.range (i + N + 1))
      (f := fun j => (1 / 2 : ℝ) ^ Nat.dist i j.val)
      (g := fun n => (1 / 2 : ℝ) ^ n)
      (fun j hj => by
        rw [Nat.dist_eq_sub_of_le (by have := (Finset.mem_filter.mp hj).2; omega)])
      (fun n _ _ => pow_nonneg (by norm_num) n)
    exact h.trans (sum_half_powers_le_two _)
  have heq := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin N => j.val ≤ i) (fun j => (1 / 2 : ℝ) ^ Nat.dist i j.val)
  change (∑ j ∈ s, (1 / 2 : ℝ) ^ Nat.dist i j.val) +
    (∑ j ∈ t, (1 / 2 : ℝ) ^ Nat.dist i j.val) = _ at heq
  linarith

def scaleWeight (i j : ℕ) : ℝ := 4 * (1 / 2 : ℝ) ^ Nat.dist i j

theorem scaleWeight_pos (i j : ℕ) : 0 < scaleWeight i j := by
  unfold scaleWeight
  positivity

theorem scaleWeight_sum (N i : ℕ) : (∑ j : Fin N, scaleWeight i j.val) ≤ 16 := by
  simp only [scaleWeight, ← Finset.mul_sum]
  linarith [sum_half_distance_le_four N i]

theorem scaleWeight_sum_column (N j : ℕ) : (∑ i : Fin N, scaleWeight i.val j) ≤ 16 := by
  simpa only [scaleWeight, Nat.dist_comm] using scaleWeight_sum N j

end LipschitzHilbert

end

end OAI
