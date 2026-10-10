import OAI.Analysis.Laughlin.Pair.Binomial
import OAI.Analysis.Laughlin.Pair.CoefficientSquare

namespace OAI

namespace Laughlin
open scoped BigOperators
open Finset Finset.Nat

theorem finite_pair_antidiagonal (Q n : ℕ) (f : ℕ → ℕ → ℝ)
    (hz : ∀ i j, Q < i ∨ Q < j → f i j = 0) :
    (∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      if x.val+y.val = n then f x.val y.val else 0) =
        ∑ ij ∈ antidiagonal n, f ij.1 ij.2 := by
  classical
  rw [← Fintype.sum_prod_type (f := fun a : Fin (Q+1) × Fin (Q+1) =>
    if a.1.val+a.2.val = n then f a.1.val a.2.val else 0)]
  refine Finset.sum_bij_ne_zero (fun a _ _ => (a.1.val,a.2.val)) ?_ ?_ ?_ ?_
  · intro a ha hn
    apply HasAntidiagonal.mem_antidiagonal.mpr
    by_contra h
    exact hn (by simp [h])
  · intro a ha hna b hb hnb hab
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst hab)
    · exact Fin.ext (congrArg Prod.snd hab)
  · rintro ⟨i,j⟩ hij hn
    have hi : i < Q+1 := by
      by_contra h
      exact hn (hz i j (Or.inl (by omega)))
    have hj : j < Q+1 := by
      by_contra h
      exact hn (hz i j (Or.inr (by omega)))
    have hs : i+j = n := HasAntidiagonal.mem_antidiagonal.mp hij
    let a : Fin (Q+1) × Fin (Q+1) := (⟨i,hi⟩,⟨j,hj⟩)
    refine ⟨a, mem_univ a, ?_, rfl⟩
    simpa [a, hs] using hn
  · intro a ha hn
    have hs : a.1.val+a.2.val = n := by
      by_contra h
      exact hn (by simp [h])
    simp [hs]

theorem pairCoefficient_unit_norm (Q p : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2) :
    (∑ x : Fin (Q+1), ∑ y : Fin (Q+1), (pairCoefficient Q p x y)^2) = 1 := by
  let f : ℕ → ℕ → ℝ := fun i j =>
    ((i : ℝ)-(j : ℝ))^2 * (Q.choose i : ℝ) * (Q.choose j : ℝ) /
      (2*(Q : ℝ)*((2*Q-2).choose p : ℝ))
  have hz : ∀ i j, Q < i ∨ Q < j → f i j = 0 := by
    intro i j h
    rcases h with h | h
    · simp [f, Nat.choose_eq_zero_of_lt h]
    · simp [f, Nat.choose_eq_zero_of_lt h]
  simp_rw [pairCoefficient_sq_choose Q p (by omega) hp]
  change (∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      if x.val+y.val = p+1 then f x.val y.val else 0) = 1
  rw [finite_pair_antidiagonal Q (p+1) f hz]
  simp only [f, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← div_eq_mul_inv]
  have hmoment : (∑ ij ∈ antidiagonal (p+1), ((ij.1 : ℝ)-(ij.2 : ℝ))^2 *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
      2*(Q : ℝ)*((2*Q-2).choose p : ℝ) := by
    have h := PairNormalization.pair_binomial_moment (Q-2) p
    have h₁ : Q-2+2 = Q := by omega
    have h₂ : 2*(Q-2)+2 = 2*Q-2 := by omega
    simpa only [h₁, h₂] using h
  rw [hmoment]
  apply div_self
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hc : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hp))
  exact mul_ne_zero (mul_ne_zero (by norm_num) hq) hc

end Laughlin

end OAI
