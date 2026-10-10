import OAI.NumberTheory.Ostmann.Arithmetic.BulkPrimeAtoms
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # Residue-dependent kernels under the exact original prime law -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem primeSubsetPrior_cell_atom {C : Type*} [Fintype C]
    (P : Finset ℕ) (q : ℕ) (a : C → ℕ) (u v : C → ℝ) (c₀ c : C) (p : P)
    (hsep : ∀ c d, c ≠ d → ¬Nat.ModEq q (a c) (a d) ∨ v c ≤ u d ∨ v d ≤ u c) :
    (∑ t ∈ primeCellSupport q a u v, (t : ℝ)⁻¹)⁻¹ * primeCellAtomWeight q (a c) (u c) (v c) p =
      if primeCellLabel q a u v c₀ p = c then primeSubsetPrior P (primeCellSupport q a u v) p else 0 := by
  have hm : (p : ℕ) ∈ primeLogCellSet q (a c) (u c) (v c) ↔
      (p : ℕ) ∈ primeCellSupport q a u v ∧ primeCellLabel q a u v c₀ p = c := by
    rw [← primeCellLabel_fiber q a u v c₀ hsep c, Finset.mem_filter]
  unfold primeCellAtomWeight primeSubsetPrior
  by_cases hp : (p : ℕ) ∈ primeCellSupport q a u v <;>
    by_cases hc : primeCellLabel q a u v c₀ p = c <;>
      simp [hm, hp, hc, div_eq_mul_inv, mul_comm]

theorem sum_coordinate_delta {J C : Type*} [Fintype J] [Fintype C]
    (label : J → C) (w : J → ℝ) (F : (J → C) → ℂ) :
    (∑ c : J → C, ((∏ j, if label j = c j then w j else 0 : ℝ) : ℂ) * F c) =
      ((∏ j, w j : ℝ) : ℂ) * F label := by
  have hp (c : J → C) : (∏ j, if label j = c j then w j else 0) =
      if label = c then ∏ j, w j else 0 := by
    by_cases hc : label = c
    · subst c; simp
    · obtain ⟨j, hj⟩ : ∃ j, label j ≠ c j := by
        by_contra h
        exact hc (funext fun j => not_not.mp (not_exists.mp h j))
      rw [ite_eq_right hc]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)
  simp_rw [hp]
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- The kernels may depend on the entire residue-cell assignment. Summing
their atomic integrals is exactly the original normalized prime expectation
of the appropriate kernel at each prime tuple. -/
theorem original_prime_cell_expansion {J C : Type*} [Fintype J] [Fintype C]
    (P : Finset ℕ) (q : J → ℕ) (a : J → C → ℕ) (u v : J → C → ℝ) (c₀ : C)
    (hP : ∀ j, primeCellSupport (q j) (a j) (u j) (v j) ⊆ P)
    (hsep : ∀ j c d, c ≠ d →
      ¬Nat.ModEq (q j) (a j c) (a j d) ∨ v j c ≤ u j d ∨ v j d ≤ u j c)
    (f : (J → C) → BulkIntegrand J) :
    let S := fun j => primeCellSupport (q j) (a j) (u j) (v j)
    let Z := fun j => (∑ p ∈ S j, (p : ℝ)⁻¹)⁻¹
    ((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C,
      ∫ y, f c y ∂Measure.pi (fun j => primeLogCellMeasure (q j) (a j (c j)) (u j (c j)) (v j (c j))) =
    ∑ x : J → P, ((∏ j, primeSubsetPrior P (S j) (x j) : ℝ) : ℂ) *
      f (fun j => primeCellLabel (q j) (a j) (u j) (v j) c₀ (x j)) (fun j => Real.log (x j : ℕ)) := by
  dsimp only
  have hcell (j : J) (c : C) : primeLogCellSet (q j) (a j c) (u j c) (v j c) ⊆ P := by
    intro p hp
    exact hP j (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, hp⟩)
  simp_rw [BulkIntegrand.integral_prime_cell_product _ P _ _ _ _ (fun j => hcell j _)]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  have hprod (c : J → C) :
      ((∏ j, (∑ p ∈ primeCellSupport (q j) (a j) (u j) (v j), (p : ℝ)⁻¹)⁻¹ : ℝ) : ℂ) *
        (((∏ j, primeCellAtomWeight (q j) (a j (c j)) (u j (c j)) (v j (c j)) (x j) : ℝ) : ℂ) *
          f c (fun j => Real.log (x j : ℕ))) =
      ((∏ j, if primeCellLabel (q j) (a j) (u j) (v j) c₀ (x j) = c j then
        primeSubsetPrior P (primeCellSupport (q j) (a j) (u j) (v j)) (x j) else 0 : ℝ) : ℂ) *
          f c (fun j => Real.log (x j : ℕ)) := by
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
    congr 2
    apply Finset.prod_congr rfl
    intro j _
    exact primeSubsetPrior_cell_atom P (q j) (a j) (u j) (v j) c₀ (c j) (x j) (hsep j)
  simp_rw [hprod]
  exact sum_coordinate_delta _ _ (fun c => f c (fun j => Real.log (x j : ℕ)))

end Ostmann

end OAI
