import OAI.Geometry.EinsteinFour.FlatDirichletNormalizer
import OAI.Geometry.EinsteinFour.ReferenceCompression

namespace OAI

/-! The flat perturbation is positive below pi/sqrt(3). -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
open scoped Topology
noncomputable section

theorem referenceMatrix_sqrt_three (t : ℝ) (N : ℕ) :
    referenceMatrix (Real.sqrt 3 * t) N = scalarDirichlet N 2 -
      (3 * (t / (N + 1)) ^ 2) • 1 := by
  have hs : (Real.sqrt 3 * t / (N + 1)) ^ 2 = 3 * (t / (N + 1)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), div_pow]
    ring
  ext i j
  simp only [referenceMatrix, scalarDirichlet, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, hs]
  by_cases hij : i = j <;> simp [hij]

theorem scaledFlatGreen_threshold_posDef (t : ℝ) (N : ℕ)
    (hRef : (referenceMatrix (Real.sqrt 3 * t) N).PosDef) :
    (1 - (3 : ℝ) • scaledFlatGreen t N).PosDef := by
  let U := scalarNormalizer (scalarDirichlet N 2)
  have hu : U * scalarDirichlet N 2 * U = 1 :=
    scalarNormalizer_normalizes (flatDirichlet_posDef N)
  have hs : U * U = flatGreen N := by
    rw [flatGreen_eq_inverse]
    exact scalarNormalizer_square (flatDirichlet_posDef N)
  have ht : Uᴴ = U := (scalarNormalizer_posSemidef _).isHermitian.eq
  have hunit : IsUnit U := (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_left_inverse hu)
  have hp := hRef.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hunit)
  rw [ht, referenceMatrix_sqrt_three] at hp
  have he : U * (scalarDirichlet N 2 - (3 * (t / (N + 1)) ^ 2) • 1) * U =
      1 - (3 : ℝ) • scaledFlatGreen t N := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hu, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hs, scaledFlatGreen, smul_smul]
  rwa [he] at hp

theorem scaledFlatGreen_eventually_below_one {t : ℝ} (ht : 0 ≤ t)
    (htop : t < Real.pi / Real.sqrt 3) :
    ∀ᶠ N : ℕ in atTop, (1 - (3 : ℝ) • scaledFlatGreen t N).PosDef := by
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : Real.sqrt 3 * t < Real.pi := by
    have h := (lt_div_iff₀ hsqrt).mp htop
    nlinarith
  filter_upwards [firstEigenvalue_eventually_pos (mul_nonneg hsqrt.le ht) hlt] with N hN
  apply scaledFlatGreen_threshold_posDef t N
  exact scalarDirichlet_posDef N _ hN

end
end PositiveEinsteinFour.Jacobi

end OAI
