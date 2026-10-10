import OAI.Probability.InvariantIsing.Cavity.CavityGaussianNodeLaw

namespace OAI

/-! The finite coordinate projection needed to select the physical
special axes from the Gaussian spectral-group block. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace InvariantIsing

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def cavityGaussianCoordinateMap (e : J → I) (z : EuclideanSpace ℝ I) :
    EuclideanSpace ℝ J := WithLp.toLp 2 (fun j => z (e j))

omit [DecidableEq J] in
lemma cavity_gaussian_coordinate_hasGaussianLaw (S : Matrix I I ℝ) (e : J → I) :
    HasGaussianLaw (cavityGaussianCoordinateMap e) (multivariateGaussian 0 S) := by
  let L : EuclideanSpace ℝ I →L[ℝ] (J → ℝ) :=
    ContinuousLinearMap.pi (fun j => EuclideanSpace.proj (e j))
  have h := ((IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian
    (0 : EuclideanSpace ℝ I) S)).map L).toLp_pi 2
  convert h using 1
  ext z j
  rfl

omit [DecidableEq J] in
lemma cavity_gaussian_coordinate_mean (S : Matrix I I ℝ) (e : J → I) :
    (∫ z, cavityGaussianCoordinateMap e z ∂multivariateGaussian 0 S) = 0 := by
  have hy := cavity_gaussian_coordinate_hasGaussianLaw S e
  ext j
  have he := (EuclideanSpace.proj j).integral_comp_comm hy.integrable
  change (∫ z, cavityGaussianCoordinateMap e z j ∂multivariateGaussian 0 S) =
    (∫ z, cavityGaussianCoordinateMap e z ∂multivariateGaussian 0 S) j at he
  rw [← he]
  have hz := (EuclideanSpace.proj (e j)).integral_comp_comm
    (IsGaussian.integrable_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ I) S))
  change (∫ z : EuclideanSpace ℝ I, z (e j) ∂multivariateGaussian 0 S) =
    (∫ z : EuclideanSpace ℝ I, z ∂multivariateGaussian 0 S) (e j) at hz
  rw [integral_id_multivariateGaussian] at hz
  exact hz

/-- Coordinate selection retains the corresponding covariance submatrix,
including degenerate Gaussian laws. -/
theorem cavity_gaussian_coordinate_law (S : Matrix I I ℝ) (hS : S.PosSemidef)
    (e : J → I) :
    (multivariateGaussian (0 : EuclideanSpace ℝ I) S).map (cavityGaussianCoordinateMap e) =
      multivariateGaussian 0 (S.submatrix e e) := by
  classical
  have hy := cavity_gaussian_coordinate_hasGaussianLaw S e
  have := hy.isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map hy.aemeasurable aestronglyMeasurable_id]
    simp only [id_eq]
    rw [cavity_gaussian_coordinate_mean, integral_id_multivariateGaussian]
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun J ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covarianceBilin_apply_eq_cov]
    · have he (i : J) : (fun x : EuclideanSpace ℝ J =>
          inner ℝ ((EuclideanSpace.basisFun J ℝ).toBasis i) x) = fun x => x i := by
        ext x
        simp [PiLp.inner_apply]
      simp_rw [he]
      rw [covariance_map_fun (by fun_prop) (by fun_prop) hy.aemeasurable,
        covariance_eval_multivariateGaussian (hS.submatrix e)]
      change cov[fun z : EuclideanSpace ℝ I => z (e i), fun z => z (e j);
        multivariateGaussian 0 S] = S (e i) (e j)
      exact covariance_eval_multivariateGaussian hS (e i) (e j)
    · exact IsGaussian.memLp_two_id
    · exact IsGaussian.memLp_two_id

end InvariantIsing

end

end OAI
