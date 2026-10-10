import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalCore

namespace OAI

/-! Entrywise errors of the bounded-size local matrices give quadratic
bounds that can be summed before any spectral approximation. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaQuadratic_entry_bound {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (B : ℝ) (hB : 0 ≤ B) (hA : ∀ i j, ‖A i j‖ ≤ B)
    (u : ι → ℂ) :
    |qmaQuadratic A u| ≤ (Fintype.card ι:ℝ)*B*(∑ i, ‖u i‖^2) := by
  have he : qmaQuadratic A u = (∑ i, ∑ j, star (u i)*(A i j*u j)).re := by
    simp [qmaQuadratic,Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [he]
  calc
    _ ≤ ‖∑ i, ∑ j, star (u i)*(A i j*u j)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ∑ j, ‖star (u i)*(A i j*u j)‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖u i‖*B*‖u j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul,norm_star]
      calc
        _ ≤ ‖u i‖*(B*‖u j‖) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring
    _ ≤ ∑ i, ∑ j, (B/2)*(‖u i‖^2+‖u j‖^2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have h := mul_nonneg hB (sq_nonneg (‖u i‖-‖u j‖))
      nlinarith
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
        nsmul_eq_mul,Finset.card_univ]
      ring

end ContinuumCoulomb

end

end OAI
