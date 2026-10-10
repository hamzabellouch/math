import OAI.Analysis.FreeEntropy.GaussianLinearTail

namespace OAI

noncomputable section
open scoped ComplexConjugate NNReal
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
 def matrixBilinear {d : ℕ} (v w : EuclideanSpace ℂ (Fin d)) (A : Matrix (Fin d) (Fin d) ℂ) : ℂ := inner ℂ v (matrixOperator A w)
 theorem matrixBilinear_trace {d : ℕ} (v w : EuclideanSpace ℂ (Fin d)) (A : Matrix (Fin d) (Fin d) ℂ) :
    matrixBilinear v w A = Matrix.trace (A * Matrix.vecMulVec (WithLp.ofLp w) (star (WithLp.ofLp v))) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  rfl
 theorem matrixBilinear_expand {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) (v w : EuclideanSpace ℂ (Fin d)) :
    matrixBilinear v w (coordinateMatrix x i) = ∑ j, ∑ k, (x (i,j,k) : ℂ)*matrixBilinear v w (hermitianBasis j k) := by
  simp_rw [matrixBilinear_trace]
  rw [coordinateMatrix_expand]
  simp [Finset.sum_mul, Matrix.trace_sum, Matrix.trace_smul]
 theorem matrixBilinear_parseval {d : ℕ} (v w : EuclideanSpace ℂ (Fin d)) :
    (∑ j, ∑ k, Complex.normSq (matrixBilinear v w (hermitianBasis j k))) = ‖v‖^2*‖w‖^2 := by
  simp_rw [matrixBilinear_trace, hermitianBasis_parseval]
  simp only [Matrix.vecMulVec_apply, map_mul, Pi.star_apply, Complex.star_def, Complex.normSq_conj]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp_rw [Complex.normSq_eq_norm_sq]
  rw [sum_comm]
  simp only [← sum_mul, ← mul_sum]
  ring
 theorem matrixBilinear_re_coeff {n d : ℕ} (i : Fin n) (v w : EuclideanSpace ℂ (Fin d)) :
    (∑ q : MatrixIndex n d, (if q.1=i then (matrixBilinear v w (hermitianBasis q.2.1 q.2.2)).re else 0)^2) ≤ ‖v‖^2*‖w‖^2 := by
  rw [Fintype.sum_prod_type]
  simp only [ite_pow, zero_pow (by norm_num : 2 ≠ 0), Fintype.sum_prod_type, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  rw [← matrixBilinear_parseval]
  apply sum_le_sum; intro j _
  apply sum_le_sum; intro k _
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg (matrixBilinear v w (hermitianBasis j k)).im]
 theorem matrixBilinear_im_coeff {n d : ℕ} (i : Fin n) (v w : EuclideanSpace ℂ (Fin d)) :
    (∑ q : MatrixIndex n d, (if q.1=i then (matrixBilinear v w (hermitianBasis q.2.1 q.2.2)).im else 0)^2) ≤ ‖v‖^2*‖w‖^2 := by
  rw [Fintype.sum_prod_type]
  simp only [ite_pow, zero_pow (by norm_num : 2 ≠ 0), Fintype.sum_prod_type, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  rw [← matrixBilinear_parseval]
  apply sum_le_sum; intro j _
  apply sum_le_sum; intro k _
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg (matrixBilinear v w (hermitianBasis j k)).re]
 theorem matrixBilinear_re_linear {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) (v w : EuclideanSpace ℂ (Fin d)) :
    (matrixBilinear v w (coordinateMatrix x i)).re = gaussianLinear (fun q : MatrixIndex n d => if q.1=i then (matrixBilinear v w (hermitianBasis q.2.1 q.2.2)).re else 0) x := by
  rw [matrixBilinear_expand]
  simp [gaussianLinear, Fintype.sum_prod_type, Complex.mul_re, mul_comm]
 theorem matrixBilinear_im_linear {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) (v w : EuclideanSpace ℂ (Fin d)) :
    (matrixBilinear v w (coordinateMatrix x i)).im = gaussianLinear (fun q : MatrixIndex n d => if q.1=i then (matrixBilinear v w (hermitianBasis q.2.1 q.2.2)).im else 0) x := by
  rw [matrixBilinear_expand]
  simp [gaussianLinear, Fintype.sum_prod_type, Complex.mul_im, mul_comm]
 theorem matrixBilinear_gaussian_tail {n d : ℕ} (i : Fin n) (v w : EuclideanSpace ℂ (Fin d))
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) {u : ℝ} (hu : 0 ≤ u) :
    (productGaussian (MatrixIndex n d)).real {x | u ≤ ‖matrixBilinear v w (coordinateMatrix x i)‖} ≤ 4*Real.exp (-u^2/8) := by
  let cr : MatrixIndex n d → ℝ := fun q => if q.1=i then (matrixBilinear v w (hermitianBasis q.2.1 q.2.2)).re else 0
  let ci : MatrixIndex n d → ℝ := fun q => if q.1=i then (matrixBilinear v w (hermitianBasis q.2.1 q.2.2)).im else 0
  have hr : (∑ q, cr q^2) ≤ (1:ℝ≥0) := by simpa [cr,hv,hw] using matrixBilinear_re_coeff i v w
  have hi : (∑ q, ci q^2) ≤ (1:ℝ≥0) := by simpa [ci,hv,hw] using matrixBilinear_im_coeff i v w
  have hsub : {x | u ≤ ‖matrixBilinear v w (coordinateMatrix x i)‖} ⊆ {x | u/2 ≤ |gaussianLinear cr x|} ∪ {x | u/2 ≤ |gaussianLinear ci x|} := by
    intro x hx
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    by_contra! hh
    have hn := Complex.norm_le_abs_re_add_abs_im (matrixBilinear v w (coordinateMatrix x i))
    rw [matrixBilinear_re_linear, matrixBilinear_im_linear] at hn
    change u ≤ _ at hx
    change |gaussianLinear cr x|+|gaussianLinear ci x| ≥ _ at hn
    linarith
  calc
    _ ≤ (productGaussian (MatrixIndex n d)).real ({x | u/2 ≤ |gaussianLinear cr x|} ∪ {x | u/2 ≤ |gaussianLinear ci x|}) := measureReal_mono hsub
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ 2*Real.exp (-(u/2)^2/(2*(1:ℝ≥0))) + 2*Real.exp (-(u/2)^2/(2*(1:ℝ≥0))) := add_le_add (gaussianLinear_tail cr 1 hr (by positivity)) (gaussianLinear_tail ci 1 hi (by positivity))
    _ = _ := by norm_num only [NNReal.coe_one]; ring_nf
end FiniteEntropySeparation

end

end OAI
