import OAI.Probability.InvariantIsing.Gaussian.HermitianQuadraticCoordinates
import OAI.Probability.InvariantIsing.Gaussian.GaussianDiagonalQuadratic

namespace OAI

/-! Exact Gaussian quadratic mean and variance in finite dimension. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

def gaussianQuadraticForm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : ℝ := ⟪x,A.toEuclideanLin x⟫

lemma gaussianQuadraticForm_continuous {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    Continuous (gaussianQuadraticForm A) := by unfold gaussianQuadraticForm; fun_prop

lemma gaussianQuadraticForm_abs_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (x : EuclideanSpace ℝ (Fin N)) :
    |gaussianQuadraticForm A x| ≤ ‖A.toEuclideanLin.toContinuousLinearMap‖*‖x‖^2 := by
  calc
    _ ≤ ‖x‖*‖A.toEuclideanLin x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖*(‖A.toEuclideanLin.toContinuousLinearMap‖*‖x‖) :=
      mul_le_mul_of_nonneg_left (A.toEuclideanLin.toContinuousLinearMap.le_opNorm x) (norm_nonneg x)
    _ = _ := by ring

lemma gaussianQuadraticForm_memLp {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    MemLp (gaussianQuadraticForm A) 2 (stdGaussian _) := by
  have hi := (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin N))) 4 (by norm_num)).integrable_norm_pow'
  apply (memLp_two_iff_integrable_sq (gaussianQuadraticForm_continuous A).aestronglyMeasurable).mpr
  apply (hi.const_mul (‖A.toEuclideanLin.toContinuousLinearMap‖^2)).mono'
    ((gaussianQuadraticForm_continuous A).pow 2).aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hh := (sq_le_sq₀ (abs_nonneg (gaussianQuadraticForm A x))
    (mul_nonneg (norm_nonneg _) (sq_nonneg ‖x‖))).2 (gaussianQuadraticForm_abs_le A x)
  simpa only [sq_abs,mul_pow,← pow_mul,Pi.pow_apply,id_eq] using hh

lemma hermitianGaussianQuadratic_mean {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    (∫ x, gaussianQuadraticForm A x ∂stdGaussian _) = A.trace := by
  let b := hA.eigenvectorBasis
  let F (g : Fin N → ℝ) := b.repr.symm (WithLp.toLp 2 g)
  have he : HasLaw b.repr.symm (stdGaussian _) (stdGaussian _) :=
    ⟨b.repr.symm.continuous.measurable.aemeasurable,stdGaussian_map b.repr.symm⟩
  have hz : HasLaw (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N))
      (stdGaussian _) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.aemeasurable,map_pi_eq_stdGaussian⟩
  have hF : HasLaw F (stdGaussian _) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) := he.comp hz
  have hdiag (g : Fin N → ℝ) : gaussianQuadraticForm A (F g) = gaussianDiagonalQuadratic hA.eigenvalues g := by
    rw [gaussianQuadraticForm,hermitian_quadratic_coordinates]
    simp only [F,b,LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [← hF.integral_comp (gaussianQuadraticForm_continuous A).aestronglyMeasurable]
  simp_rw [Function.comp_def,hdiag]
  rw [gaussianDiagonalQuadratic_mean,hA.trace_eq_sum_eigenvalues]
  simp

lemma hermitianGaussianQuadratic_variance {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    variance (gaussianQuadraticForm A) (stdGaussian _) = 2*∑ i, (hA.eigenvalues i)^2 := by
  let b := hA.eigenvectorBasis
  let F (g : Fin N → ℝ) := b.repr.symm (WithLp.toLp 2 g)
  have he : HasLaw b.repr.symm (stdGaussian _) (stdGaussian _) :=
    ⟨b.repr.symm.continuous.measurable.aemeasurable,stdGaussian_map b.repr.symm⟩
  have hz : HasLaw (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N))
      (stdGaussian _) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.aemeasurable,map_pi_eq_stdGaussian⟩
  have hF : HasLaw F (stdGaussian _) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) := he.comp hz
  have hdiag : gaussianQuadraticForm A ∘ F = gaussianDiagonalQuadratic hA.eigenvalues := by
    funext g
    change ⟪F g,A.toEuclideanLin (F g)⟫ = _
    rw [hermitian_quadratic_coordinates]
    simp only [F,b,LinearIsometryEquiv.apply_symm_apply]
    rfl
  calc
    _ = variance (gaussianQuadraticForm A ∘ F) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) := by
      rw [← hF.map_eq]
      exact variance_map ((gaussianQuadraticForm_continuous A).measurable.aemeasurable) hF.aemeasurable
    _ = _ := by rw [hdiag,gaussianDiagonalQuadratic_variance]

end InvariantIsing

end

end OAI
