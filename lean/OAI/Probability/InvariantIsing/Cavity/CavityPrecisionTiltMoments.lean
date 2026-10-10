import OAI.Probability.InvariantIsing.Cavity.CavityGaussianSpectral
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace OAI

/-! Laplace transforms of the positive-precision quadratic Gaussian tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityPrecisionPotential {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (l z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (‖z‖ ^ 2 - ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) Q z⟫) / 2 + ⟪l, z⟫

lemma cavity_precision_potential_integrable {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef) (l : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z => Real.exp (cavityPrecisionPotential Q l z))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  cavity_gaussian_precision_integrable Q hQ l

lemma cavity_precision_potential_integral {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef) (l : EuclideanSpace ℝ (Fin d)) :
    (∫ z, Real.exp (cavityPrecisionPotential Q l z)
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (Real.sqrt Q.det)⁻¹ *
        Real.exp (⟪l, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l⟫ / 2) :=
  cavity_gaussian_precision_integral Q hQ l

lemma cavity_precision_inverse_square {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (l v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    (⟪l + t • v, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ (l + t • v)⟫ -
      ⟪l, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l⟫) / 2 =
      t * ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l⟫ +
        t ^ 2 / 2 * ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ v⟫ := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ.inv.isHermitian l v
  change ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l, v⟫ =
    ⟪l, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ v⟫ at hs
  have hc := real_inner_comm v (Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l)
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [← hs, hc]
  ring

theorem cavity_precision_tilt_mgf {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (l v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    mgf (fun z => ⟪v, z⟫)
      ((stdGaussian (EuclideanSpace ℝ (Fin d))).tilted (cavityPrecisionPotential Q l)) t =
      Real.exp (t * ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l⟫ +
        t ^ 2 / 2 * ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ v⟫) := by
  rw [mgf, integral_exp_tilted]
  have he : cavityPrecisionPotential Q l + (fun z => t * ⟪v, z⟫) =
      cavityPrecisionPotential Q (l + t • v) := by
    funext z
    simp only [cavityPrecisionPotential, Pi.add_apply, inner_add_left, real_inner_smul_left]
    ring
  rw [he, cavity_precision_potential_integral Q hQ,
    cavity_precision_potential_integral Q hQ]
  have hn : (Real.sqrt Q.det)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hQ.det_pos).ne'
  rw [mul_div_mul_left _ _ hn, ← Real.exp_sub]
  congr 1
  rw [← sub_div, cavity_precision_inverse_square Q hQ]

theorem cavity_multivariate_gaussian_mgf {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (m v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    mgf (fun z => ⟪v, z⟫) (multivariateGaussian m S) t =
      Real.exp (t * ⟪v, m⟫ + t ^ 2 / 2 * ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) S v⟫) := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) := innerSL ℝ v
  have hm : (∫ z, L z ∂multivariateGaussian m S) = ⟪v, m⟫ := by
    rw [L.integral_comp_id_comm IsGaussian.integrable_id, integral_id_multivariateGaussian]
    rfl
  have hv : Var[L; multivariateGaussian m S] =
      ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) S v⟫ := by
    change Var[fun z => ⟪v, z⟫; multivariateGaussian m S] = _
    rw [← covarianceBilin_self IsGaussian.memLp_two_id v,
      covarianceBilin_multivariateGaussian hS, Matrix.inner_toEuclideanCLM]
  have hLaw : HasLaw L (gaussianReal ⟪v, m⟫
      (⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) S v⟫).toNNReal) (multivariateGaussian m S) := by
    refine ⟨L.measurable.aemeasurable, ?_⟩
    rw [IsGaussian.map_eq_gaussianReal, hm, hv]
  have hp : 0 ≤ ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) S v⟫ := by
    rw [← hv]
    exact variance_nonneg _ _
  calc
    _ = Real.exp (⟪v, m⟫ * t +
        (⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) S v⟫).toNNReal * t ^ 2 / 2) :=
      mgf_gaussianReal hLaw t
    _ = _ := by
      rw [Real.coe_toNNReal _ hp]
      congr 1
      ring

end InvariantIsing

end

end OAI
