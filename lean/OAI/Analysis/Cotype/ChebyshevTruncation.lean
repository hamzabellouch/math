import OAI.Analysis.Cotype.ChebyshevBounds

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Polynomial.Chebyshev
namespace Cotype

def chebyshevTruncation {n : ℕ} (c : Fin (n+1) → ℝ) (d : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d), c j • T ℝ (j : ℕ)

theorem card_low_indices_le (n d : ℕ) :
    (Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d)).card ≤ d+1 := by
  let s := Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d)
  have hsub : s.image Fin.val ⊆ Finset.range (d+1) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hj).2)
  calc
    s.card = (s.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.range (d+1)).card := Finset.card_le_card hsub
    _ = d+1 := Finset.card_range _

theorem chebyshevTruncation_bound {n : ℕ} (c : Fin (n+1) → ℝ) (d : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |(chebyshevExpansion c).eval x| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(chebyshevTruncation c d).eval x| ≤ 2*M*(d+1) := by
  simp only [chebyshevTruncation, eval_finsetSum, eval_smul, smul_eq_mul]
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d),
        |c j * (T ℝ (j : ℕ)).eval x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d), 2*M := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul (chebyshevExpansion_coefficient_bound c hM hQ j)
        (chebyshev_abs_le_one j hx) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ ≤ 2*M*(d+1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : ((Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d)).card : ℝ) ≤ d+1 := by
        exact_mod_cast card_low_indices_le n d
      nlinarith

theorem chebyshevRemainder_bound {n : ℕ} (c : Fin (n+1) → ℝ) (d : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |(chebyshevExpansion c).eval x| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(chebyshevExpansion c - chebyshevTruncation c d).eval x| ≤ 3*M*(d+1) := by
  rw [eval_sub]
  have h := abs_sub_le ((chebyshevExpansion c).eval x) 0 ((chebyshevTruncation c d).eval x)
  simp only [sub_zero, zero_sub, abs_neg] at h
  have htr := chebyshevTruncation_bound c d hM hQ hx
  have hqx := hQ x hx
  nlinarith [mul_nonneg hM (Nat.cast_nonneg (α := ℝ) d)]

end Cotype

end

end OAI
