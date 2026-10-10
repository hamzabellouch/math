import OAI.Geometry.EinsteinFour.HighestActionCoordinates
import OAI.Geometry.EinsteinFour.TensorPairing

namespace OAI

/-! The plus Casimir energy and curvature bound on actual highest Hessians. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- The Casimir identity for four-slot tensors. -/
theorem totalPlus_casimir (c : Fin 21 → ℝ) :
    totalPlus 0 (totalPlus 0 (highest c)) +
      totalPlus 1 (totalPlus 1 (highest c)) +
      totalPlus 2 (totalPlus 2 (highest c)) = (-48 : ℝ) • highest c := by
  simp_rw [totalPlus_highest]
  rw [← highest_add, ← highest_add, coordinate_casimir, highest_smul]

/-- Entrywise identification with the four-slot Kronecker-sum matrix. -/
theorem totalPlus_coordinates (s : Fin 3) (X : Hessian) (p : TensorIndex) :
    tensorCoordinates (totalPlus s X) p =
      ∑ q : TensorIndex, plusKernel s p q * tensorCoordinates X q := by
  rcases p with ⟨i, j, a, b⟩
  simp [tensorCoordinates, totalPlus, matrixAction_row_sum, plusKernel,
    Fintype.sum_prod_type, add_mul, Finset.sum_add_distrib, ite_mul, ite_and]
  ring

/-- The actual total generator is skew-adjoint for the Frobenius pairing. -/
theorem totalPlus_skew (s : Fin 3) (X Y : Hessian) :
    hessianPairing (totalPlus s X) Y = -hessianPairing X (totalPlus s Y) := by
  have h := skew_matrix_pairing (plusKernel s) (plusKernel_skew s)
    (tensorCoordinates X) (tensorCoordinates Y)
  simp_rw [← totalPlus_coordinates] at h
  rw [tensorCoordinates_pairing, tensorCoordinates_pairing] at h
  exact h

/-- Exact energy Casimir on the genuine twenty-one-dimensional tensors. -/
theorem totalPlus_energy (c : Fin 21 → ℝ) :
    hessianNormSq (totalPlus 0 (highest c)) +
      hessianNormSq (totalPlus 1 (highest c)) +
      hessianNormSq (totalPlus 2 (highest c)) = 48 * hessianNormSq (highest c) := by
  have h0 := totalPlus_skew 0 (totalPlus 0 (highest c)) (highest c)
  have h1 := totalPlus_skew 1 (totalPlus 1 (highest c)) (highest c)
  have h2 := totalPlus_skew 2 (totalPlus 2 (highest c)) (highest c)
  have h := congrArg (fun X => hessianPairing X (highest c)) (totalPlus_casimir c)
  simp only [hessianPairing_add_left, hessianPairing_smul_left] at h
  rw [h0, h1, h2] at h
  simp only [hessianPairing_self] at h
  linarith

/-- The sharp plus-curvature coefficient follows directly from the energy
Casimir and the three lower eigenvalue bounds. -/
theorem plus_energy_bound (c : Fin 21 → ℝ) (t : Fin 3 → ℝ) (x : ℝ)
    (ht : ∀ s, -x ≤ t s) :
    -(t 0 * hessianNormSq (totalPlus 0 (highest c)) +
      t 1 * hessianNormSq (totalPlus 1 (highest c)) +
      t 2 * hessianNormSq (totalPlus 2 (highest c))) / 60 ≤
      (4 / 5) * x * hessianNormSq (highest c) := by
  have hn (s : Fin 3) : 0 ≤ hessianNormSq (totalPlus s (highest c)) := by
    unfold hessianNormSq
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h0 := mul_nonneg (show 0 ≤ t 0 + x by linarith [ht 0]) (hn 0)
  have h1 := mul_nonneg (show 0 ≤ t 1 + x by linarith [ht 1]) (hn 1)
  have h2 := mul_nonneg (show 0 ≤ t 2 + x by linarith [ht 2]) (hn 2)
  have hc := congrArg (fun r : ℝ => x * r) (totalPlus_energy c)
  nlinarith

/-- The energy identity applies to any tensor satisfying the actual local
symmetry, trace and differentiated Bianchi conditions. -/
theorem totalPlus_energy_of_condition (X : Hessian) (hX : condition X) :
    hessianNormSq (totalPlus 0 X) + hessianNormSq (totalPlus 1 X) +
      hessianNormSq (totalPlus 2 X) = 48 * hessianNormSq X := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  exact totalPlus_energy c

theorem plus_energy_bound_of_condition (X : Hessian) (hX : condition X)
    (t : Fin 3 → ℝ) (x : ℝ) (ht : ∀ s, -x ≤ t s) :
    -(t 0 * hessianNormSq (totalPlus 0 X) +
      t 1 * hessianNormSq (totalPlus 1 X) +
      t 2 * hessianNormSq (totalPlus 2 X)) / 60 ≤
      (4 / 5) * x * hessianNormSq X := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  exact plus_energy_bound c t x ht

end
end PositiveEinsteinFour.HighestHessian

end OAI
