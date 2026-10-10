import OAI.Geometry.EinsteinFour.HighestMinusCoordinates

namespace OAI

/-! The minus Casimir energy and curvature bound on actual highest Hessians. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- The actual total-minus Casimir is spin one. -/
theorem totalMinus_casimir (c : Fin 21 → ℝ) :
    totalMinus 0 (totalMinus 0 (highest c)) +
      totalMinus 1 (totalMinus 1 (highest c)) +
      totalMinus 2 (totalMinus 2 (highest c)) = (-8 : ℝ) • highest c := by
  simp_rw [totalMinus_highest]
  rw [← highest_add, ← highest_add, minus_coordinate_casimir, highest_smul]

def minusKernel (s : Fin 3) (p q : TensorIndex) : ℝ :=
  (if p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2
    then rightQuaternion s p.1 q.1 else 0) +
  (if p.1 = q.1 ∧ p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2
    then rightQuaternion s p.2.1 q.2.1 else 0)

theorem rightQuaternion_skew (s : Fin 3) (i j : Fin 4) :
    rightQuaternion s i j = -rightQuaternion s j i := by
  fin_cases s <;> fin_cases i <;> fin_cases j <;> norm_num [rightQuaternion]

theorem minusKernel_skew (s : Fin 3) (p q : TensorIndex) :
    minusKernel s p q = -minusKernel s q p := by
  unfold minusKernel
  rw [rightQuaternion_skew s p.1 q.1, rightQuaternion_skew s p.2.1 q.2.1]
  simp only [eq_comm (a := q.1) (b := p.1),
    eq_comm (a := q.2.1) (b := p.2.1),
    eq_comm (a := q.2.2.1) (b := p.2.2.1),
    eq_comm (a := q.2.2.2) (b := p.2.2.2)]
  split_ifs <;> ring

theorem totalMinus_coordinates (s : Fin 3) (X : Hessian) (p : TensorIndex) :
    tensorCoordinates (totalMinus s X) p =
      ∑ q : TensorIndex, minusKernel s p q * tensorCoordinates X q := by
  rcases p with ⟨i, j, a, b⟩
  simp [tensorCoordinates, totalMinus, minusKernel,
    Fintype.sum_prod_type, add_mul, Finset.sum_add_distrib, ite_mul, ite_and]

theorem totalMinus_skew (s : Fin 3) (X Y : Hessian) :
    hessianPairing (totalMinus s X) Y = -hessianPairing X (totalMinus s Y) := by
  have h := skew_matrix_pairing (minusKernel s) (minusKernel_skew s)
    (tensorCoordinates X) (tensorCoordinates Y)
  simp_rw [← totalMinus_coordinates] at h
  rw [tensorCoordinates_pairing, tensorCoordinates_pairing] at h
  exact h

theorem totalMinus_energy (c : Fin 21 → ℝ) :
    hessianNormSq (totalMinus 0 (highest c)) +
      hessianNormSq (totalMinus 1 (highest c)) +
      hessianNormSq (totalMinus 2 (highest c)) = 8 * hessianNormSq (highest c) := by
  have h0 := totalMinus_skew 0 (totalMinus 0 (highest c)) (highest c)
  have h1 := totalMinus_skew 1 (totalMinus 1 (highest c)) (highest c)
  have h2 := totalMinus_skew 2 (totalMinus 2 (highest c)) (highest c)
  have h := congrArg (fun X => hessianPairing X (highest c)) (totalMinus_casimir c)
  simp only [hessianPairing_add_left, hessianPairing_smul_left] at h
  rw [h0, h1, h2] at h
  simp only [hessianPairing_self] at h
  linarith

/-- The minus curvature bound has exactly the coefficient needed by P. -/
theorem minus_energy_bound (c : Fin 21 → ℝ) (u : Fin 3 → ℝ) (y : ℝ)
    (hu : ∀ s, -y ≤ u s) :
    -(u 0 * hessianNormSq (totalMinus 0 (highest c)) +
      u 1 * hessianNormSq (totalMinus 1 (highest c)) +
      u 2 * hessianNormSq (totalMinus 2 (highest c))) / 4 ≤
      2 * y * hessianNormSq (highest c) := by
  have hn (s : Fin 3) : 0 ≤ hessianNormSq (totalMinus s (highest c)) := by
    unfold hessianNormSq
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h0 := mul_nonneg (show 0 ≤ u 0 + y by linarith [hu 0]) (hn 0)
  have h1 := mul_nonneg (show 0 ≤ u 1 + y by linarith [hu 1]) (hn 1)
  have h2 := mul_nonneg (show 0 ≤ u 2 + y by linarith [hu 2]) (hn 2)
  have hc := congrArg (fun r : ℝ => y * r) (totalMinus_energy c)
  nlinarith

/-- The minus energy identity applies to every actual constrained Hessian. -/
theorem totalMinus_energy_of_condition (X : Hessian) (hX : condition X) :
    hessianNormSq (totalMinus 0 X) + hessianNormSq (totalMinus 1 X) +
      hessianNormSq (totalMinus 2 X) = 8 * hessianNormSq X := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  exact totalMinus_energy c

theorem minus_energy_bound_of_condition (X : Hessian) (hX : condition X)
    (u : Fin 3 → ℝ) (y : ℝ) (hu : ∀ s, -y ≤ u s) :
    -(u 0 * hessianNormSq (totalMinus 0 X) +
      u 1 * hessianNormSq (totalMinus 1 X) +
      u 2 * hessianNormSq (totalMinus 2 X)) / 4 ≤
      2 * y * hessianNormSq X := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  exact minus_energy_bound c u y hu

end
end PositiveEinsteinFour.HighestHessian

end OAI
