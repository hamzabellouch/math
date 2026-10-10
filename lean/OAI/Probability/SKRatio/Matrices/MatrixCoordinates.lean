import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKRatioGaussian
abbrev MatrixCoordinates (ι : Type*) := (ι × ι) ⊕ ι

variable {ι : Type*}

def goeMatrix (r : ℝ) (g : MatrixCoordinates ι → ℝ) : Matrix ι ι ℝ :=
  fun i k => sqrt (2*r)/2 * (g (.inl (i,k)) + g (.inl (k,i)))

variable [Fintype ι]

def rawCoordinateMatrix (g : MatrixCoordinates ι → ℝ) : Matrix ι ι ℝ :=
  fun i k => g (.inl (i,k))

lemma rawCoordinateMatrix_norm (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖rawCoordinateMatrix g‖ ≤ ‖g‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← sq]
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow,Real.sq_sqrt (by positivity),
    EuclideanSpace.norm_sq_eq]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,Fintype.sum_sum_type,Fintype.sum_prod_type,
    rawCoordinateMatrix]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma goeMatrix_norm (r : ℝ) (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖goeMatrix r g‖ ≤ sqrt (2*r)*‖g‖ := by
  have he : goeMatrix r g = (sqrt (2*r)/2) •
      (rawCoordinateMatrix g+(rawCoordinateMatrix g)ᵀ) := by ext; rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (sqrt (2*r)/2)*(‖rawCoordinateMatrix g‖+‖(rawCoordinateMatrix g)ᵀ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = sqrt (2*r)*‖rawCoordinateMatrix g‖ := by rw [Matrix.frobenius_norm_transpose]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (rawCoordinateMatrix_norm g) (sqrt_nonneg _)

omit [Fintype ι] in
lemma goeMatrix_sub (r : ℝ) (g h : MatrixCoordinates ι → ℝ) :
    goeMatrix r (g-h) = goeMatrix r g-goeMatrix r h := by
  ext i k; simp only [goeMatrix,Pi.sub_apply,Matrix.sub_apply]; ring

lemma goeMatrix_L2_lipschitz (r : ℝ) :
    LipschitzWith ⟨sqrt (2*r),sqrt_nonneg _⟩
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) => goeMatrix r g) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  simpa only [dist_eq_norm,← goeMatrix_sub] using! goeMatrix_norm r (g-h)

lemma goeMatrix_pi_lipschitz (r : ℝ) :
    LipschitzWith (⟨sqrt (2*r),sqrt_nonneg _⟩ *
      (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
      (goeMatrix (ι := ι) r) := by
  exact (goeMatrix_L2_lipschitz (ι := ι) r).comp
    (PiLp.lipschitzWith_toLp 2 (fun _ : MatrixCoordinates ι => ℝ))

variable [DecidableEq ι]

def symmetricElementary (a b : ι) : Matrix ι ι ℝ :=
  Matrix.single a b 1+Matrix.single b a 1

omit [Fintype ι] in
lemma goeMatrix_update (r : ℝ) (g : MatrixCoordinates ι → ℝ) (a b : ι) (t : ℝ) :
    goeMatrix r (Function.update g (.inl (a,b)) t) =
      goeMatrix r g + ((sqrt (2*r)/2)*(t-g (.inl (a,b)))) • symmetricElementary a b := by
  ext i k
  simp only [goeMatrix,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,symmetricElementary,
    Matrix.single_apply]
  by_cases hi : i=a <;> by_cases hk : k=b <;> by_cases hi' : i=b <;> by_cases hk' : k=a <;>
    simp_all [Function.update_apply,Prod.ext_iff,eq_comm] <;> ring

lemma symmetricElementary_norm_le (a b : ι) : ‖symmetricElementary a b‖ ≤ 2 := by
  unfold symmetricElementary
  exact (norm_add_le _ _).trans (by simpa [Matrix.frobenius_norm_def,Matrix.single_apply,ite_and] using (show (1:ℝ)+1 ≤ 2 by norm_num))

lemma goeMatrix_updated_hasDerivAt (r : ℝ) (g : MatrixCoordinates ι → ℝ) (a b : ι) :
    HasDerivAt (fun t => goeMatrix r (Function.update g (.inl (a,b)) t))
      ((sqrt (2*r)/2) • symmetricElementary a b) (g (.inl (a,b))) := by
  simp_rw [goeMatrix_update]
  have ha := (hasDerivAt_id (g (.inl (a,b)))).sub_const (g (.inl (a,b)))
  have hb := ha.const_mul (sqrt (2*r)/2)
  have hh := (hb.smul_const (symmetricElementary a b)).const_add (goeMatrix r g)
  simpa only [mul_one,id_eq] using! hh

end SKRatioGaussian

end
end
end
end

end OAI
