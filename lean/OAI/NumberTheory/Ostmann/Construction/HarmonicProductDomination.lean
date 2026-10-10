import OAI.NumberTheory.Ostmann.Construction.HarmonicUnitPriors
import OAI.NumberTheory.Ostmann.Characters.TreeLeafIndex

namespace OAI

/-! # Original independent harmonic priors on the leaves of a transfer tree -/

namespace Ostmann

open scoped BigOperators Classical

private theorem product_cellPrior_indexed {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (μ : I → A → ℝ) (cell : I → A → B) (y : I → B) :
    (∏ i, cellPrior (μ i) (cell i) (y i)) =
      ∑ x : I → A, if (fun i => cell i (x i)) = y then ∏ i, μ i (x i) else 0 := by
  classical
  unfold cellPrior
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : (fun i => cell i (x i)) = y
  · have hi (i : I) : cell i (x i) = y i := congrFun he i
    simp [hi]
  · have hi : ∃ i, cell i (x i) ≠ y i := by
      by_contra hn
      apply he
      funext i
      exact not_not.mp (not_exists.mp hn i)
    obtain ⟨i, hi⟩ := hi
    rw [ite_eq_right he]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem indexed_cell_expectation_eq {I A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
    (μ : I → A → ℝ) (cell : I → A → B) (F : (I → B) → ℝ) :
    (∑ x : I → A, (∏ i, μ i (x i)) * F (fun i => cell i (x i))) =
      ∑ y : I → B, (∏ i, cellPrior (μ i) (cell i) (y i)) * F y := by
  simp_rw [product_cellPrior_indexed, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- A pointwise upper bound for each residue class yields the product of
exactly one loss for each independently sampled leaf. -/
theorem indexed_cell_expectation_le {I A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
    (μ : I → A → ℝ) (cell : I → A → B) (C : I → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a)
    (hcell : ∀ i b, cellPrior (μ i) (cell i) b ≤ C i * (Fintype.card B : ℝ)⁻¹)
    (F : (I → B) → ℝ) (hF : ∀ y, 0 ≤ F y) :
    (∑ x : I → A, (∏ i, μ i (x i)) * F (fun i => cell i (x i))) ≤
      (∏ i, C i) * ((Fintype.card (I → B) : ℝ)⁻¹ * ∑ y : I → B, F y) := by
  rw [indexed_cell_expectation_eq]
  have hprod (y : I → B) :
      (∏ i, cellPrior (μ i) (cell i) (y i)) ≤
        (∏ i, C i) * (Fintype.card (I → B) : ℝ)⁻¹ := by
    calc
      _ ≤ ∏ i, (C i * (Fintype.card B : ℝ)⁻¹) :=
        Finset.prod_le_prod₀ (fun i _ => cellPrior_nonneg (μ i) (cell i) (hμ i) _) (fun i _ => hcell i _)
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fun,
          Nat.cast_pow, inv_pow]
  calc
    _ ≤ ∑ y : I → B, ((∏ i, C i) * (Fintype.card (I → B) : ℝ)⁻¹) * F y :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hprod y) (hF y)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- This uses each leaf's actual harmonic subset, with all boundary primes
retained, and produces the original uniform-unit tree average. -/
theorem harmonic_leaf_residue_domination (P : Finset ℕ) (q n : ℕ) [NeZero q]
    (S : TreeLeafIndex n → Finset ℕ) (h J : TreeLeafIndex n → ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime q)
    (hsmall : ∀ i, q ≤ 2 ^ h i)
    (hrange : ∀ i p, p ∈ S i → 2 ^ h i ≤ p ∧ p < 2 ^ (h i + J i))
    (F : TreeLeafTuple (ZMod q)ˣ n → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ x : TreeLeafIndex n → P, (∏ i, primeSubsetPrior P (S i) (x i)) *
      F ((treeLeafTupleEquiv (ZMod q)ˣ n).symm
        (fun i => ZMod.unitOfCoprime (x i : ℕ) (hunit (x i))))) ≤
      (∏ i, (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)) *
        ((Fintype.card (TreeLeafTuple (ZMod q)ˣ n) : ℝ)⁻¹ * ∑ y, F y) := by
  have hb := indexed_cell_expectation_le
    (fun i => primeSubsetPrior P (S i))
    (fun _ p => ZMod.unitOfCoprime (p : ℕ) (hunit p))
    (fun i => (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹ * (3 * J i))
    (fun _ => primeSubsetPrior_nonneg _ _)
    (fun i b => primeSubsetPrior_unit_residue_le P (S i) q (h i) (J i)
      hunit (hsmall i) (hrange i) b)
    (fun y => F ((treeLeafTupleEquiv (ZMod q)ˣ n).symm y)) (fun y => hF _)
  rw [(treeLeafTupleEquiv (ZMod q)ˣ n).symm.sum_comp F] at hb
  rw [Fintype.card_congr (treeLeafTupleEquiv (ZMod q)ˣ n)]
  exact hb

end Ostmann

end OAI
