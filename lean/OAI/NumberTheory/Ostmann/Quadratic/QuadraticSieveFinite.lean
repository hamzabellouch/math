import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveTranspose
import OAI.NumberTheory.Ostmann.Preliminaries.FiniteMatrixDuality

namespace OAI

/-! # Finite quadratic-sieve bounds and their reciprocity symmetry

These are the elementary initial steps of Heath-Brown (1995), sections 2--3.
The bound predicate refers to the actual Jacobi matrix and finite coefficients.
-/

namespace Ostmann

open Matrix
open scoped BigOperators Classical

/-- A bound for the actual finite odd-squarefree Jacobi matrix. -/
def QuadraticSieveBound (M N : ℕ) (K : ℝ) : Prop :=
  ∀ b : ℕ → ℂ, (∑ m ∈ oddSquarefreeRange M, ‖quadraticSieveSum N b m‖ ^ 2) ≤
    K * quadraticSieveEnergy N b

 theorem oddSquarefreeRange_card_le (N : ℕ) : (oddSquarefreeRange N).card ≤ N := by
  calc
    _ ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
    _ = N := by simp

 theorem quadraticSieveSum_trivial (N m : ℕ) (b : ℕ → ℂ) :
    ‖quadraticSieveSum N b m‖ ^ 2 ≤ (N : ℝ) * quadraticSieveEnergy N b := by
  let I := oddSquarefreeRange N
  let u : I → ℂ := fun n => (jacobiSym (n.val : ℤ) m : ℂ)
  let v : I → ℂ := fun n => b n.val
  have hh := finite_complex_cauchy_schwarz u v
  have hid : star u ⬝ᵥ v = quadraticSieveSum N b m := by
    change (∑ n : I, star ((jacobiSym (n.val : ℤ) m : ℂ)) * b n.val) = _
    calc
      _ = ∑ n ∈ I, star ((jacobiSym (n : ℤ) m : ℂ)) * b n :=
        Finset.sum_coe_sort I (fun n : ℕ => star ((jacobiSym (n : ℤ) m : ℂ)) * b n)
      _ = quadraticSieveSum N b m := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [star_intCast]
        ring
  have hu : (∑ n : I, ‖u n‖ ^ 2) ≤ N := by
    calc
      _ ≤ ∑ _n : I, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        rcases jacobiSym.trichotomy (n.val : ℤ) m with h | h | h <;> simp [u, h]
      _ = (I.card : ℝ) := by simp
      _ ≤ N := by exact_mod_cast oddSquarefreeRange_card_le N
  have hv : (∑ n : I, ‖v n‖ ^ 2) = quadraticSieveEnergy N b := by
    exact Finset.sum_coe_sort I (fun n : ℕ => ‖b n‖ ^ 2)
  rw [hid, hv] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hu (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

 theorem quadraticSieveBound_trivial (M N : ℕ) : QuadraticSieveBound M N ((M : ℝ) * N) := by
  intro b
  have hE : 0 ≤ quadraticSieveEnergy N b := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ ≤ ∑ _m ∈ oddSquarefreeRange M, (N : ℝ) * quadraticSieveEnergy N b := by
      exact Finset.sum_le_sum (fun m _ => quadraticSieveSum_trivial N m b)
    _ = (oddSquarefreeRange M).card * ((N : ℝ) * quadraticSieveEnergy N b) := by simp
    _ ≤ (M : ℝ) * ((N : ℝ) * quadraticSieveEnergy N b) := by
      gcongr
      exact_mod_cast oddSquarefreeRange_card_le M
    _ = _ := by ring

 theorem quadraticTranspose_of_bound {M N : ℕ} {K : ℝ}
    (h : QuadraticSieveBound M N K) (b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b m‖ ^ 2) ≤
      2 * K * quadraticSieveEnergy N b := by
  have h1 := h b
  have h3 := h (reciprocityTwist b)
  rw [quadraticSieveEnergy_reciprocityTwist] at h3
  have ht : (∑ u ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b u‖ ^ 2) ≤
      (∑ u ∈ oddSquarefreeRange M, ‖quadraticSieveSum N b u‖ ^ 2) +
      ∑ u ∈ oddSquarefreeRange M, ‖quadraticSieveSum N (reciprocityTwist b) u‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u hu
    have huodd := (Finset.mem_filter.mp hu).2.1
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp huodd) with hu1 | hu3
    · rw [quadraticTransposeSum_one_mod_four N b u hu1]
      linarith [sq_nonneg ‖quadraticSieveSum N (reciprocityTwist b) u‖]
    · rw [quadraticTransposeSum_three_mod_four N b u hu3]
      linarith [sq_nonneg ‖quadraticSieveSum N b u‖]
  nlinarith

end Ostmann

end OAI
