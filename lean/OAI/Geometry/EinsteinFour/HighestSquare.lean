import OAI.Geometry.EinsteinFour.HighestCurvature

namespace OAI

/-! The weighted positive square on the actual highest-Hessian arrays. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

private theorem tensorCoordinates_add (X Y : Hessian) (p : TensorIndex) :
    tensorCoordinates (X + Y) p = tensorCoordinates X p + tensorCoordinates Y p := rfl

private theorem tensorCoordinates_smul (r : ℝ) (X : Hessian) (p : TensorIndex) :
    tensorCoordinates (r • X) p = r * tensorCoordinates X p := rfl

theorem totalPlus_add (s : Fin 3) (X Y : Hessian) :
    totalPlus s (X + Y) = totalPlus s X + totalPlus s Y := by
  funext i j a b
  change tensorCoordinates (totalPlus s (X + Y)) (i, j, a, b) =
    tensorCoordinates (totalPlus s X) (i, j, a, b) +
      tensorCoordinates (totalPlus s Y) (i, j, a, b)
  simp only [totalPlus_coordinates, tensorCoordinates_add, mul_add,
    Finset.sum_add_distrib]

theorem totalPlus_smul (s : Fin 3) (r : ℝ) (X : Hessian) :
    totalPlus s (r • X) = r • totalPlus s X := by
  funext i j a b
  change tensorCoordinates (totalPlus s (r • X)) (i, j, a, b) =
    r * tensorCoordinates (totalPlus s X) (i, j, a, b)
  simp only [totalPlus_coordinates, tensorCoordinates_smul, mul_left_comm,
    ← Finset.mul_sum]

theorem totalMinus_add (s : Fin 3) (X Y : Hessian) :
    totalMinus s (X + Y) = totalMinus s X + totalMinus s Y := by
  funext i j a b
  change tensorCoordinates (totalMinus s (X + Y)) (i, j, a, b) =
    tensorCoordinates (totalMinus s X) (i, j, a, b) +
      tensorCoordinates (totalMinus s Y) (i, j, a, b)
  simp only [totalMinus_coordinates, tensorCoordinates_add, mul_add,
    Finset.sum_add_distrib]

theorem totalMinus_smul (s : Fin 3) (r : ℝ) (X : Hessian) :
    totalMinus s (r • X) = r • totalMinus s X := by
  funext i j a b
  change tensorCoordinates (totalMinus s (r • X)) (i, j, a, b) =
    r * tensorCoordinates (totalMinus s X) (i, j, a, b)
  simp only [totalMinus_coordinates, tensorCoordinates_smul, mul_left_comm,
    ← Finset.mul_sum]

/-- The symmetric form of the concrete curvature operator. -/
def curvaturePairing (t u : Fin 3 → ℝ) (X Y : Hessian) : ℝ :=
  4 * hessianPairing X Y +
    (∑ s, t s * hessianPairing (totalPlus s X) (totalPlus s Y)) / 24 +
    (∑ s, u s * hessianPairing (totalMinus s X) (totalMinus s Y)) / 4

theorem curvaturePairing_self (t u : Fin 3 → ℝ) (X : Hessian) :
    curvaturePairing t u X X = casimirCurvatureForm t u X := by
  simp only [curvaturePairing, casimirCurvatureForm, hessianPairing_self]

theorem curvaturePairing_comm (t u : Fin 3 → ℝ) (X Y : Hessian) :
    curvaturePairing t u X Y = curvaturePairing t u Y X := by
  simp only [curvaturePairing, hessianPairing_comm]

theorem curvaturePairing_add_left (t u : Fin 3 → ℝ) (X Y Z : Hessian) :
    curvaturePairing t u (X + Y) Z =
      curvaturePairing t u X Z + curvaturePairing t u Y Z := by
  simp only [curvaturePairing, totalPlus_add, totalMinus_add,
    hessianPairing_add_left, mul_add, Finset.sum_add_distrib]
  ring

theorem curvaturePairing_smul_left (t u : Fin 3 → ℝ) (r : ℝ) (X Y : Hessian) :
    curvaturePairing t u (r • X) Y = r * curvaturePairing t u X Y := by
  have h (a b : ℝ) : a * (r * b) = r * (a * b) := by ring
  simp only [curvaturePairing, totalPlus_smul, totalMinus_smul,
    hessianPairing_smul_left, h, ← Finset.mul_sum]
  ring

theorem curvaturePairing_add_right (t u : Fin 3 → ℝ) (X Y Z : Hessian) :
    curvaturePairing t u X (Y + Z) =
      curvaturePairing t u X Y + curvaturePairing t u X Z := by
  rw [curvaturePairing_comm t u X, curvaturePairing_add_left,
    curvaturePairing_comm t u Y, curvaturePairing_comm t u Z]

theorem curvaturePairing_smul_right (t u : Fin 3 → ℝ) (r : ℝ) (X Y : Hessian) :
    curvaturePairing t u X (r • Y) = r * curvaturePairing t u X Y := by
  rw [curvaturePairing_comm t u X, curvaturePairing_smul_left,
    curvaturePairing_comm t u Y]

/-- The exact weighted-square expansion, before any geometric integration. -/
theorem weighted_curvature_square_identity (t u : Fin 3 → ℝ) (X Y : Hessian)
    (m : ℝ) (hm : m ≠ 0) :
    (m / 6) * curvaturePairing t u (X + (1 / (2 * m)) • Y)
      (X + (1 / (2 * m)) • Y) =
    (m / 6) * curvaturePairing t u X X + curvaturePairing t u X Y / 6 +
      curvaturePairing t u Y Y / (24 * m) := by
  rw [curvaturePairing_add_left]
  simp only [curvaturePairing_add_right, curvaturePairing_smul_left,
    curvaturePairing_smul_right]
  rw [curvaturePairing_comm t u Y X]
  field_simp [hm]
  ring

/-- Positivity of the actual highest-Hessian operator gives the weighted
square used in the Hessian argument. -/
theorem weighted_curvature_square_nonneg (c d : Fin 21 → ℝ)
    (t u : Fin 3 → ℝ) (x y m : ℝ) (hm : 0 < m)
    (ht : ∀ s, -x ≤ t s) (hu : ∀ s, -y ≤ u s) (hxy : x + y ≤ 2) :
    0 ≤ (m / 6) * curvaturePairing t u (highest c) (highest c) +
      curvaturePairing t u (highest c) (highest d) / 6 +
      curvaturePairing t u (highest d) (highest d) / (24 * m) := by
  rw [← weighted_curvature_square_identity t u (highest c) (highest d) m hm.ne']
  simp_rw [← highest_smul, ← highest_add]
  rw [curvaturePairing_self]
  exact mul_nonneg (by positivity)
    (casimirCurvatureForm_nonneg (c + (1 / (2 * m)) • d) t u x y ht hu hxy)

/-- The weighted square in intrinsic tensor form, with only the concrete
highest-Hessian constraints as hypotheses. -/
theorem weighted_curvature_square_nonneg_of_condition (X Y : Hessian)
    (hX : condition X) (hY : condition Y) (t u : Fin 3 → ℝ)
    (x y m : ℝ) (hm : 0 < m) (ht : ∀ s, -x ≤ t s)
    (hu : ∀ s, -y ≤ u s) (hxy : x + y ≤ 2) :
    0 ≤ (m / 6) * curvaturePairing t u X X + curvaturePairing t u X Y / 6 +
      curvaturePairing t u Y Y / (24 * m) := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  obtain ⟨d, rfl⟩ := exists_highest Y hY
  exact weighted_curvature_square_nonneg c d t u x y m hm ht hu hxy

end
end PositiveEinsteinFour.HighestHessian

end OAI
