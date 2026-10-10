import OAI.Geometry.EinsteinFour.HighestMinusForm
import OAI.Geometry.EinsteinFour.HighestSquare

namespace OAI

/-! The sharp anti-self-dual upper cost on actual derivative tensors. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open TraceHessian

/-- Simultaneous right-quaternion action on the two derivative slots. -/
def rightTwist (s : Fin 3) (X : Hessian) : Hessian := fun i j a b =>
  ∑ k, ∑ l, rightQuaternion s i k * rightQuaternion s j l * X k l a b

/-- The four orthogonal sectors of the two real quaternion slots. -/
def rightSector (r : Fin 4) (X : Hessian) : Hessian := fun i j a b =>
  (X i j a b +
    (if r = 0 ∨ r = 1 then 1 else -1) * rightTwist 0 X i j a b +
    (if r = 0 ∨ r = 2 then 1 else -1) * rightTwist 1 X i j a b +
    (if r = 0 ∨ r = 3 then 1 else -1) * rightTwist 2 X i j a b) / 4

private theorem rightSector_partition_slice (X : Hessian) (a b : Fin 3) :
    (∑ r : Fin 4, ∑ i, ∑ j, rightSector r X i j a b ^ 2) =
      ∑ i, ∑ j, X i j a b ^ 2 := by
  simp [rightSector, rightTwist, rightQuaternion, Fin.sum_univ_succ]
  ring

/-- The sector squared norms sum to the actual tensor squared norm. -/
theorem rightSector_partition (X : Hessian) :
    (∑ r : Fin 4, hessianNormSq (rightSector r X)) = hessianNormSq X := by
  simp only [hessianNormSq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact rightSector_partition_slice X a b

private theorem rightSector_twist_slice_0 (X : Hessian) (a b : Fin 3) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      rightQuaternion 0 i k * rightQuaternion 0 j l * X k l a b * X i j a b) =
      2 * (∑ i, ∑ j, rightSector 0 X i j a b ^ 2) +
      2 * (∑ i, ∑ j, rightSector 1 X i j a b ^ 2) -
      ∑ r : Fin 4, ∑ i, ∑ j, rightSector r X i j a b ^ 2 := by
  simp [rightSector, rightTwist, rightQuaternion, Fin.sum_univ_succ]
  ring

private theorem rightSector_twist_slice_1 (X : Hessian) (a b : Fin 3) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      rightQuaternion 1 i k * rightQuaternion 1 j l * X k l a b * X i j a b) =
      2 * (∑ i, ∑ j, rightSector 0 X i j a b ^ 2) +
      2 * (∑ i, ∑ j, rightSector 2 X i j a b ^ 2) -
      ∑ r : Fin 4, ∑ i, ∑ j, rightSector r X i j a b ^ 2 := by
  simp [rightSector, rightTwist, rightQuaternion, Fin.sum_univ_succ]
  ring

private theorem rightSector_twist_slice_2 (X : Hessian) (a b : Fin 3) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      rightQuaternion 2 i k * rightQuaternion 2 j l * X k l a b * X i j a b) =
      2 * (∑ i, ∑ j, rightSector 0 X i j a b ^ 2) +
      2 * (∑ i, ∑ j, rightSector 3 X i j a b ^ 2) -
      ∑ r : Fin 4, ∑ i, ∑ j, rightSector r X i j a b ^ 2 := by
  simp [rightSector, rightTwist, rightQuaternion, Fin.sum_univ_succ]
  ring

private theorem rightSector_twist_slice (s : Fin 3) (X : Hessian) (a b : Fin 3) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      rightQuaternion s i k * rightQuaternion s j l * X k l a b * X i j a b) =
      2 * (∑ i, ∑ j, rightSector 0 X i j a b ^ 2) +
      2 * (∑ i, ∑ j, rightSector s.succ X i j a b ^ 2) -
      ∑ r : Fin 4, ∑ i, ∑ j, rightSector r X i j a b ^ 2 := by
  fin_cases s
  · exact rightSector_twist_slice_0 X a b
  · exact rightSector_twist_slice_1 X a b
  · exact rightSector_twist_slice_2 X a b

/-- Exact simultaneous spectral decomposition, proved from the real matrices. -/
theorem rightDerivativeSlotForm_sector (s : Fin 3) (X : Hessian) :
    rightDerivativeSlotForm s X = 2 * hessianNormSq (rightSector 0 X) +
      2 * hessianNormSq (rightSector s.succ X) - hessianNormSq X := by
  unfold rightDerivativeSlotForm
  simp_rw [rightSector_twist_slice]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  change 2 * hessianNormSq (rightSector 0 X) +
    2 * hessianNormSq (rightSector s.succ X) -
      (∑ a, ∑ b, ∑ r : Fin 4, ∑ i, ∑ j, rightSector r X i j a b ^ 2) = _
  simp_rw [rightSector_partition_slice]
  rfl

/-- The anti-self-dual form is a weighted sum of the three nontrivial sectors. -/
theorem minusDerivativeCurvatureForm_sector (u : Fin 3 → ℝ)
    (hu : ∑ s, u s = 0) (X : Hessian) :
    minusDerivativeCurvatureForm u X =
      ∑ s, u s * hessianNormSq (rightSector s.succ X) := by
  simp only [minusDerivativeCurvatureForm, rightDerivativeSlotForm_sector]
  have ht := congrArg (fun z : ℝ => z *
    (2 * hessianNormSq (rightSector 0 X) - hessianNormSq X)) hu
  simp only [Fin.sum_univ_three] at ht ⊢
  nlinarith

/-- The sharp cost has coefficient one, including all boundary cases. -/
theorem minusDerivativeCurvatureForm_lower (u : Fin 3 → ℝ)
    (hu : ∑ s, u s = 0) (y : ℝ) (hy : 0 ≤ y)
    (huy : ∀ s, -y ≤ u s) (X : Hessian) :
    -y * hessianNormSq X ≤ minusDerivativeCurvatureForm u X := by
  rw [minusDerivativeCurvatureForm_sector u hu]
  have hp := rightSector_partition X
  have hn (r : Fin 4) : 0 ≤ hessianNormSq (rightSector r X) := by
    unfold hessianNormSq
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h0 := mul_nonneg hy (hn 0)
  have h1 := mul_nonneg (show 0 ≤ u 0 + y by linarith [huy 0]) (hn 1)
  have h2 := mul_nonneg (show 0 ≤ u 1 + y by linarith [huy 1]) (hn 2)
  have h3 := mul_nonneg (show 0 ≤ u 2 + y by linarith [huy 2]) (hn 3)
  simp only [Fin.sum_univ_four] at hp
  simp only [Fin.sum_univ_three]
  rw [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
    show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
  nlinarith


/-- The full two-derivative space has minus Casimir energy at most eight. -/
theorem totalMinus_energy_le (X : Hessian) :
    (∑ s : Fin 3, hessianNormSq (totalMinus s X)) ≤ 8 * hessianNormSq X := by
  have hp := rightSector_partition X
  have hn : 0 ≤ hessianNormSq (rightSector 0 X) := by
    unfold hessianNormSq
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp only [Fin.sum_univ_four] at hp
  simp only [Fin.sum_univ_three, totalMinus_square, rightDerivativeSlotForm_sector]
  rw [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
    show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
  nlinarith

/-- A full-space coercive estimate whenever the plus energy is the already
computed spin-three value; the minus estimate requires no type assumption. -/
theorem curvaturePairing_nonneg_of_plus_energy
    (t u : Fin 3 → ℝ) (x y : ℝ) (X : Hessian)
    (ht : ∀ s, -x ≤ t s) (hu : ∀ s, -y ≤ u s)
    (hy : 0 ≤ y) (hxy : x + y ≤ 2)
    (hplus : (∑ s : Fin 3, hessianNormSq (totalPlus s X)) = 48 * hessianNormSq X) :
    0 ≤ curvaturePairing t u X X := by
  have hn (Y : Hessian) : 0 ≤ hessianNormSq Y := by
    unfold hessianNormSq
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT (s : Fin 3) := mul_nonneg (show 0 ≤ t s + x by linarith [ht s])
    (hn (totalPlus s X))
  have hU (s : Fin 3) := mul_nonneg (show 0 ≤ u s + y by linarith [hu s])
    (hn (totalMinus s X))
  have hM := mul_le_mul_of_nonneg_left (totalMinus_energy_le X) hy
  have hC := mul_nonneg (show 0 ≤ 4 - 2*x - 2*y by linarith) (hn X)
  simp only [curvaturePairing, hessianPairing_self, Fin.sum_univ_three] at hplus hM ⊢
  nlinarith [hT 0, hT 1, hT 2, hU 0, hU 1, hU 2]

end
end PositiveEinsteinFour.HighestHessian

end OAI
