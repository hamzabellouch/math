import OAI.Analysis.Steinitz.Scales

namespace OAI

/-! Scalar and matrix Gaussian tail estimates. -/

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace GaussianTail

lemma integral_exp_square (t : ℝ) :
    (∫ x : ℝ, Real.exp (-t * x ^ 2 / 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 + t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have he (x : ℝ) : gaussianPDFReal 0 1 x * Real.exp (-t * x ^ 2 / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 + t) / 2) * x ^ 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp only [smul_eq_mul, he, integral_const_mul, integral_gaussian]
  rw [show Real.pi / ((1 + t) / 2) = (2 * Real.pi) / (1 + t) by rw [div_div_eq_mul_div]; ring]
  rw [Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
  have hp : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

lemma integrable_exp_square {t : ℝ} (ht : -1 < t) :
    Integrable (fun x : ℝ => Real.exp (-t * x ^ 2 / 2)) (gaussianReal 0 1) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_square t]
  exact ne_of_gt (inv_pos.mpr (Real.sqrt_pos.mpr (by linarith)))

lemma inverse_sqrt_one_sub_le_exp {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1/2) :
    (Real.sqrt (1-u))⁻¹ ≤ Real.exp u := by
  have hpos : 0 < 1-u := by linarith
  have hlog : -Real.log (1-u) ≤ 2*u := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at h
    have hi : (1-u)⁻¹ - 1 ≤ 2*u := by
      rw [inv_eq_one_div]
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hpos).mpr
      nlinarith
    exact h.trans hi
  apply (Real.log_le_log_iff (inv_pos.mpr (Real.sqrt_pos.mpr hpos)) (Real.exp_pos u)).mp
  rw [Real.log_inv, Real.log_sqrt hpos.le, Real.log_exp]
  linarith

open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma quadratic_eigenbasis {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (x : ι → ℝ) :
    ⟪∑ i, x i • hA.eigenvectorBasis i,
      toEuclideanCLM (𝕜 := ℝ) A (∑ i, x i • hA.eigenvectorBasis i)⟫ =
      ∑ i, hA.eigenvalues i * x i ^ 2 := by
  have he (i : ι) : toEuclideanCLM (𝕜 := ℝ) A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    apply WithLp.ofLp_injective
    exact hA.mulVec_eigenvectorBasis i
  simp only [map_sum, map_smul, he, smul_smul,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    hA.eigenvectorBasis.inner_eq_ite]
  simp [mul_ite, ite_mul, pow_two, mul_comm, mul_left_comm, mul_assoc]

lemma quadratic_mgf_eq {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ / 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) = ∏ i, (Real.sqrt (1-hA.eigenvalues i))⁻¹ := by
  have he (x : ι → ℝ) :
      Real.exp (⟪∑ i, x i • hA.eigenvectorBasis i,
        toEuclideanCLM (𝕜 := ℝ) A (∑ i, x i • hA.eigenvectorBasis i)⟫ / 2) =
      ∏ i, Real.exp (hA.eigenvalues i * x i ^ 2 / 2) := by
    rw [quadratic_eigenbasis, ← Real.exp_sum]
    congr 1
    simp only [Finset.sum_div]
  rw [stdGaussian_eq_map_pi_orthonormalBasis hA.eigenvectorBasis,
    integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  simp only [he]
  rw [integral_fintype_prod_eq_prod
    (f := fun i (x : ℝ) => Real.exp (hA.eigenvalues i * x ^ 2 / 2))]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [neg_neg, sub_eq_add_neg] using integral_exp_square (-hA.eigenvalues i)

lemma quadratic_mgf_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hEig : ∀ i, hA.1.eigenvalues i ≤ 1/2) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ / 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) ≤ Real.exp A.trace := by
  rw [quadratic_mgf_eq hA.1, hA.1.trace_eq_sum_eigenvalues,
    Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro i _
    positivity
  · intro i _
    exact inverse_sqrt_one_sub_le_exp (hA.eigenvalues_nonneg i) (hEig i)

lemma quadratic_mgf_integrable {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hEig : ∀ i, hA.eigenvalues i < 1) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ / 2))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  apply Integrable.of_integral_ne_zero
  rw [quadratic_mgf_eq hA]
  apply ne_of_gt
  exact Finset.prod_pos fun i _ => inv_pos.mpr (Real.sqrt_pos.mpr (by linarith [hEig i]))

lemma quadratic_tail {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hEig : ∀ i, hA.1.eigenvalues i ≤ 1/2) (r : ℝ) :
    stdGaussian (EuclideanSpace ℝ ι)
      {x | 2*(A.trace+r) ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫} ≤
        ENNReal.ofReal (Real.exp (-r)) := by
  let f := fun x : EuclideanSpace ℝ ι =>
    Real.exp (-A.trace-r) * Real.exp (⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫/2)
  have hi : Integrable f (stdGaussian (EuclideanSpace ℝ ι)) :=
    (quadratic_mgf_integrable hA.1 (fun i => by linarith [hEig i])).const_mul _
  have hbound := hi.measure_le_integral (Filter.Eventually.of_forall fun x =>
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    (s := {x | 2*(A.trace+r) ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫})
    (fun x hx => by
      dsimp only [f]
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by
        change 2*(A.trace+r) ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ at hx
        linarith))
  apply hbound.trans
  apply ENNReal.ofReal_le_ofReal
  rw [show (∫ x, f x ∂stdGaussian (EuclideanSpace ℝ ι)) =
      Real.exp (-A.trace-r) * ∫ x, Real.exp (⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫/2)
        ∂stdGaussian (EuclideanSpace ℝ ι) by exact integral_const_mul _ _]
  calc
    _ ≤ Real.exp (-A.trace-r) * Real.exp A.trace :=
      mul_le_mul_of_nonneg_left (quadratic_mgf_le hA hEig) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma eigenvalue_le_of_form_le {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {b : ℝ}
    (hb : ∀ x : EuclideanSpace ℝ ι, ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ ≤ b*‖x‖^2) :
    ∀ i, hA.eigenvalues i ≤ b := by
  intro i
  have h := hb (hA.eigenvectorBasis i)
  rw [hA.eigenvectorBasis.orthonormal.norm_eq_one, one_pow, mul_one] at h
  have he : toEuclideanCLM (𝕜 := ℝ) A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    apply WithLp.ofLp_injective
    exact hA.mulVec_eigenvectorBasis i
  simpa [he, real_inner_smul_right, hA.eigenvectorBasis.inner_eq_ite] using h

lemma scaled_quadratic_tail {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {b : ℝ} (hb : 0 < b)
    (hform : ∀ x : EuclideanSpace ℝ ι, ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ ≤ b*‖x‖^2)
    (r : ℝ) :
    stdGaussian (EuclideanSpace ℝ ι)
      {x | 2*A.trace+4*b*r ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫} ≤
        ENNReal.ofReal (Real.exp (-r)) := by
  let S : Matrix ι ι ℝ := (1/(2*b)) • A
  have hS : S.PosSemidef := hA.smul (by positivity : 0 ≤ 1/(2*b))
  have he (x : EuclideanSpace ℝ ι) : ⟪x, toEuclideanCLM (𝕜 := ℝ) S x⟫ =
      (1/(2*b))*⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ := by
    simp only [S, inner_toEuclideanCLM, smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hspec : ∀ i, hS.1.eigenvalues i ≤ 1/2 := by
    apply eigenvalue_le_of_form_le hS.1
    intro x
    rw [he]
    have hx := mul_le_mul_of_nonneg_left (hform x) (by positivity : 0 ≤ 1/(2*b))
    apply hx.trans_eq
    field_simp
  have hset : {x : EuclideanSpace ℝ ι | 2*S.trace+2*r ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) S x⟫} =
      {x | 2*A.trace+4*b*r ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫} := by
    ext x
    change (2*S.trace+2*r ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) S x⟫) ↔
      2*A.trace+4*b*r ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫
    simp only [he, S, trace_smul, smul_eq_mul]
    constructor <;> intro h
    · have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*b)
      field_simp at hm
      nlinarith
    · have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1/(2*b))
      field_simp at hm ⊢
      nlinarith
  have ht := quadratic_tail hS hspec r
  rw [show 2*(S.trace+r)=2*S.trace+2*r by ring, hset] at ht
  exact ht

end GaussianTail

end

section

open Matrix MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
namespace GaussianTail
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

noncomputable def matrixMap (B : Matrix κ ι ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  (Matrix.toEuclideanLin B).toContinuousLinearMap

noncomputable def squareMass (B : Matrix κ ι ℝ) : ℝ := ∑ i,∑ j,B i j^2

omit [DecidableEq ι] in
lemma squareMass_nonneg (B : Matrix κ ι ℝ) : 0 ≤ squareMass B := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma gram_form (B : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) :
    ⟪x,toEuclideanCLM (𝕜 := ℝ) (B.transpose*B) x⟫ = ‖matrixMap B x‖^2 := by
  rw [inner_toEuclideanCLM,← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  rw [← real_inner_self_eq_norm_sq]
  rfl

omit [DecidableEq ι] in
lemma gram_trace (B : Matrix κ ι ℝ) : (B.transpose*B).trace = squareMass B := by
  change (∑ i,∑ j,B j i*B j i) = ∑ i,∑ j,B i j^2
  simp only [← sq]
  exact Finset.sum_comm

lemma norm_sq_le_squareMass (B : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) :
    ‖matrixMap B x‖^2 ≤ squareMass B*‖x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  change (∑ i,(∑ j,B i j*x j)^2) ≤ (∑ i,∑ j,B i j^2)*(∑ j,x j^2)
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma matrix_square_tail (B : Matrix κ ι ℝ) {b : ℝ} (hb : 0 < b)
    (hB : ∀ x : EuclideanSpace ℝ ι,‖matrixMap B x‖^2 ≤ b*‖x‖^2) (r : ℝ) :
    stdGaussian (EuclideanSpace ℝ ι) {x | 2*squareMass B+4*b*r ≤ ‖matrixMap B x‖^2} ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  have hA : (B.transpose*B).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self B
  simpa only [gram_trace,gram_form] using scaled_quadratic_tail hA hb
    (fun x => by rw [gram_form]; exact hB x) r

lemma interpolated_form (B : Matrix κ ι ℝ) {v : ℝ} (hv : 0 ≤ v)
    (hS : squareMass B ≤ v) (hB : ∀ x : EuclideanSpace ℝ ι,‖matrixMap B x‖^2 ≤ 4*‖x‖^2) :
    ∀ x : EuclideanSpace ℝ ι,‖matrixMap B x‖^2 ≤ (2*Real.sqrt v)*‖x‖^2 := by
  intro x
  by_cases h : v ≤ 4
  · apply (norm_sq_le_squareMass B x).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply hS.trans
    have hs := Real.sq_sqrt hv
    have hp := Real.sqrt_nonneg v
    have hle : Real.sqrt v ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith⟩
    nlinarith
  · apply (hB x).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hs := Real.sq_sqrt hv
    have hp := Real.sqrt_nonneg v
    have hle : 2 ≤ Real.sqrt v := (Real.le_sqrt (by norm_num) hv).mpr (by linarith)
    linarith

lemma interpolated_tail (B : Matrix κ ι ℝ) {v : ℝ} (hv : 0 < v)
    (hS : squareMass B ≤ v) (hB : ∀ x : EuclideanSpace ℝ ι,‖matrixMap B x‖^2 ≤ 4*‖x‖^2)
    (r : ℝ) :
    stdGaussian (EuclideanSpace ℝ ι) {x | 2*v+8*Real.sqrt v*r ≤ ‖matrixMap B x‖^2} ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  apply (measure_mono (show {x | 2*v+8*Real.sqrt v*r ≤ ‖matrixMap B x‖^2} ⊆
    {x | 2*squareMass B+4*(2*Real.sqrt v)*r ≤ ‖matrixMap B x‖^2} from ?_)).trans
  · exact matrix_square_tail B (by positivity) (interpolated_form B hv.le hS hB) r
  · intro x hx
    change 2*v+8*Real.sqrt v*r ≤ ‖matrixMap B x‖^2 at hx
    change 2*squareMass B+4*(2*Real.sqrt v)*r ≤ ‖matrixMap B x‖^2
    linarith

end GaussianTail

end

end OAI
