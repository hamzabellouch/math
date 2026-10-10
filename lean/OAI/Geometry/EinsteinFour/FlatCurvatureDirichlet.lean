import OAI.Geometry.EinsteinFour.FlatDirichletThreshold
import OAI.Geometry.EinsteinFour.JacobiCurvatureCap
import OAI.Geometry.EinsteinFour.JacobiSchemeMatrix

namespace OAI

/-! The actual flat Green normalization of the curvature Dirichlet form. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
noncomputable section

theorem scalarLift_smul {N : ℕ} (c : ℝ) (G : Matrix (Fin N) (Fin N) ℝ) :
    scalarLift (c • G) = c • scalarLift G := by
  ext ⟨a,i⟩ ⟨b,j⟩
  change (1 : NormalMatrix) a b * (c * G i j) = c * ((1 : NormalMatrix) a b * G i j)
  ring

theorem flat_curvatureDirichlet_eq {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix) :
    curvatureDirichlet t (fun i => R i - 1) =
      scalarLift (scalarDirichlet N 2) - (t / (N + 1)) ^ 2 • Matrix.blockDiagonal R := by
  rw [curvatureDirichlet_eq, scalarLift_sub_diagonal]
  simp only [add_sub_cancel]

theorem flat_curvatureDirichlet_normalized {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix) :
    scalarLift (scalarNormalizer (scalarDirichlet N 2)) *
      curvatureDirichlet t (fun i => R i - 1) *
      scalarLift (scalarNormalizer (scalarDirichlet N 2)) =
        1 - symmetricCurvatureKernel (flatGreenRoot t N) R := by
  rw [flat_curvatureDirichlet_eq, Matrix.mul_sub, Matrix.sub_mul,
    ← scalarLift_mul, ← scalarLift_mul,
    scalarNormalizer_normalizes (flatDirichlet_posDef N), scalarLift_one,
    Matrix.mul_smul, Matrix.smul_mul, symmetricCurvatureKernel,
    flatGreenRoot, scalarLift_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul]
  rw [pow_two]

theorem flat_curvatureDirichlet_posDef {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix)
    (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3)
    (hscalar : (1 - (3 : ℝ) • scaledFlatGreen t N).PosDef) :
    (curvatureDirichlet t (fun i => R i - 1)).PosDef := by
  let U := scalarNormalizer (scalarDirichlet N 2)
  have hn : U * scalarDirichlet N 2 * U = 1 :=
    scalarNormalizer_normalizes (flatDirichlet_posDef N)
  have hu : IsUnit (scalarLift U) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [det_scalarLift]
    exact (Matrix.isUnit_det_of_left_inverse hn).pow 3
  have hUt : Uᵀ = U := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (scalarNormalizer_posSemidef (scalarDirichlet N 2)).isHermitian.eq
  apply hu.posDef_star_left_conjugate_iff.mp
  rw [Matrix.star_eq_conjTranspose, scalarLift_conjTranspose U hUt,
    flat_curvatureDirichlet_normalized]
  exact symmetricCurvatureKernel_one_sub_posDef _ _ (flatGreenRoot_square t N)
    (flatGreenRoot_transpose t N) hscalar R hR

theorem flat_curvatureDirichlet_eventually_posDef {t : ℝ} (ht : 0 ≤ t)
    (htop : t < Real.pi / Real.sqrt 3)
    (R : ℕ → ℝ → NormalMatrix)
    (hR : ∀ N s, (R N s).PosSemidef ∧ (R N s).trace = 3)
    (τ : ℕ → ℕ → ℝ) :
    ∀ᶠ N : ℕ in atTop, (curvatureDirichlet t
      (fun i : Fin N => R N (τ N i.val) - 1)).PosDef := by
  filter_upwards [scaledFlatGreen_eventually_below_one ht htop] with N hN
  exact flat_curvatureDirichlet_posDef t _ (fun i => hR N _) hN

end
end PositiveEinsteinFour.Jacobi

end OAI
