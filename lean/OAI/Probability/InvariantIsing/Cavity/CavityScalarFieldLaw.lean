import OAI.Probability.InvariantIsing.Cavity.CavityScalarSpin
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianImage
import OAI.Probability.InvariantIsing.Cavity.CavitySpectralStack

namespace OAI

/-! A scalar covariance compression of the transformed Gaussian cavity
field is exactly a product of independent one-site Gaussian laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace NNReal

namespace InvariantIsing

theorem cavity_rectangularGaussian_image {d n : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (B : Matrix (Fin n) (Fin d) ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S).map
      B.toEuclideanLin.toContinuousLinearMap =
        multivariateGaussian 0 (B * S * B.transpose) := by
  let L := B.toEuclideanLin.toContinuousLinearMap
  have hp : (B * S * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.mul_mul_conjTranspose_same B
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [L.integral_id_map IsGaussian.integrable_id]
    simp only [integral_id_multivariateGaussian, map_zero]
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id L,
      covarianceBilin_multivariateGaussian hS, covarianceBilin_multivariateGaussian hp]
    rw [← Matrix.inner_toEuclideanCLM S, ContinuousLinearMap.adjoint_inner_left,
      show L.adjoint = B.transpose.toEuclideanLin.toContinuousLinearMap from
        cavity_rectangular_adjoint B,
      ← Matrix.inner_toEuclideanCLM (B * S * B.transpose)]
    congr 1
    ext i
    change (B *ᵥ (S *ᵥ (B.transpose *ᵥ fun j => y j))) i =
      ((B * S * B.transpose) *ᵥ fun j => y j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem cavity_scalarGaussian_ofLp_law (n : ℕ) (v : ℝ≥0) :
    MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → Fin n → ℝ)
      (multivariateGaussian 0 ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
      (vectorGaussianLaw n v : Measure (Fin n → ℝ)) := by
  let T := MeasurableEquiv.toLp 2 (Fin n → ℝ)
  let scale : (Fin n → ℝ) → Fin n → ℝ := fun z i => (NNReal.sqrt v : ℝ) * z i
  have hscale : MeasurePreserving scale
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (vectorGaussianLaw n v : Measure (Fin n → ℝ)) := by
    apply measurePreserving_pi
    intro i
    refine ⟨by fun_prop, ?_⟩
    have hs : NNReal.mk ((NNReal.sqrt v : ℝ) ^ 2) (sq_nonneg _) = v := by
      apply Subtype.ext
      change (NNReal.sqrt v : ℝ) ^ 2 = (v : ℝ)
      norm_cast
      exact NNReal.sq_sqrt v
    simpa only [hs, mul_zero, mul_one] using
      gaussianReal_map_const_mul (μ := 0) (v := 1) (NNReal.sqrt v : ℝ)
  have hT : MeasurePreserving T
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hmap : (vectorGaussianLaw n v : Measure (Fin n → ℝ)).map T =
      multivariateGaussian 0 ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    rw [← hscale.map_eq, Measure.map_map T.measurable hscale.measurable]
    rw [multivariateGaussian, cavity_sqrt_scalar_identity _ v.coe_nonneg]
    have he : (fun x : EuclideanSpace ℝ (Fin n) =>
        (0 : EuclideanSpace ℝ (Fin n)) +
          Matrix.toEuclideanCLM (𝕜 := ℝ) ((Real.sqrt (v : ℝ)) • 1) x) =
        (fun x => (NNReal.sqrt v : ℝ) • x) := by
      funext x
      simp only [map_smul, map_one, smul_apply, one_apply_eq_self, zero_add,
        Real.coe_sqrt]
    rw [he, ← hT.map_eq,
      Measure.map_map (show Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
        (NNReal.sqrt v : ℝ) • x) from by fun_prop) T.measurable]
    congr 1
  exact MeasurePreserving.symm T ⟨T.measurable, hmap⟩

/-- Once a transformed covariance is scalar, the actual projected field
has the product law used by the one-site recursion. -/
theorem cavity_scalar_projected_field_law {d n : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (L : Matrix (Fin d) (Fin n) ℝ) (v : ℝ≥0)
    (hcov : L.transpose * S * L = (v : ℝ) • 1) :
    MeasurePreserving (fun z : EuclideanSpace ℝ (Fin d) =>
      WithLp.ofLp (L.transpose.toEuclideanLin z))
      (multivariateGaussian 0 S) (vectorGaussianLaw n v : Measure (Fin n → ℝ)) := by
  have hm := cavity_rectangularGaussian_image S hS L.transpose
  simp only [Matrix.transpose_transpose, hcov] at hm
  have hL : MeasurePreserving L.transpose.toEuclideanLin.toContinuousLinearMap
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S)
      (multivariateGaussian 0 ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) :=
    ⟨by fun_prop, hm⟩
  exact (cavity_scalarGaussian_ofLp_law n v).comp hL

end InvariantIsing

end

end OAI
