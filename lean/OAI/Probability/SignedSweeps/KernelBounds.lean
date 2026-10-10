import OAI.Probability.SignedSweeps.TupleRealization

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]

def kernelOperator (K : I → J → ℝ) : EuclideanSpace ℂ J →ₗ[ℂ] EuclideanSpace ℂ I where
  toFun f := WithLp.toLp 2 (fun i => ∑ j, (K i j : ℂ) * f j)
  map_add' f g := by ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext i
    change (∑ j, (K i j : ℂ) * (c * f j)) = c * ∑ j, (K i j : ℂ) * f j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

omit [Fintype I] in
@[simp] lemma kernelOperator_apply (K : I → J → ℝ) (f : EuclideanSpace ℂ J) (i : I) :
    kernelOperator K f i = ∑ j, (K i j : ℂ) * f j := rfl

omit [Fintype I] in
lemma kernelOperator_comp (K : I → J → ℝ) (M : J → L → ℝ) :
    (kernelOperator K).comp (kernelOperator M) =
      kernelOperator (fun i l => ∑ j, K i j * M j l) := by
  ext f i
  simp only [LinearMap.comp_apply, kernelOperator_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

lemma kernelOperator_adjoint (K : I → J → ℝ) :
    (kernelOperator K).adjoint = kernelOperator (fun j i => K i j) := by
  apply LinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [LinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply, kernelOperator_apply, RCLike.inner_apply, map_sum,
    map_mul, Complex.conj_ofReal,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_left_comm, mul_assoc]

lemma nonnegative_symmetric_kernel_quadratic_bound (K : I → I → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hsym : ∀ i j, K i j = K j i)
    {p : ℝ} (hrow : ∀ i, (∑ j, K i j) ≤ p) (f : EuclideanSpace ℂ I) :
    (inner ℂ f (kernelOperator K f)).re ≤ p * ‖f‖ ^ 2 := by
  have ht (i j : I) : ((star (f i)) * ((K i j : ℂ) * f j)).re ≤
      K i j * ((‖f i‖ ^ 2 + ‖f j‖ ^ 2) / 2) := by
    calc
      _ ≤ ‖star (f i) * ((K i j : ℂ) * f j)‖ := Complex.re_le_norm _
      _ = K i j * (‖f i‖ * ‖f j‖) := by
        rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK i j)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖f i‖ - ‖f j‖)]) (hK i j)
  calc
    _ = ∑ i, ∑ j, ((star (f i)) * ((K i j : ℂ) * f j)).re := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, kernelOperator_apply, Finset.sum_mul,
        Complex.re_sum, Complex.star_def]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring
    _ ≤ ∑ i, ∑ j, K i j * ((‖f i‖ ^ 2 + ‖f j‖ ^ 2) / 2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ht i j))
    _ = ∑ i, (∑ j, K i j) * ‖f i‖ ^ 2 := by
      simp_rw [mul_div, mul_add, add_div]
      simp only [Finset.sum_add_distrib]
      have he : (∑ i, ∑ j, K i j * ‖f j‖ ^ 2 / 2) =
          ∑ i, ∑ j, K i j * ‖f i‖ ^ 2 / 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym]
      rw [he]
      simp_rw [← Finset.sum_div, ← Finset.sum_mul]
      ring
    _ ≤ ∑ i, p * ‖f i‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum, EuclideanSpace.norm_sq_eq]

theorem nonnegative_kernel_opNorm_sq_le (K : I → J → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) {p : ℝ} (hp : 0 ≤ p)
    (hrow : ∀ i, (∑ i', ∑ j, K i j * K i' j) ≤ p) :
    ‖(kernelOperator K).toContinuousLinearMap‖ ^ 2 ≤ p := by
  let T := kernelOperator K
  have hq (f : EuclideanSpace ℂ I) : ‖T.adjoint f‖ ^ 2 ≤ p * ‖f‖ ^ 2 := by
    have he : (inner ℂ (T.adjoint f) (T.adjoint f)).re = ‖T.adjoint f‖ ^ 2 := by
      simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
        ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [← he, LinearMap.adjoint_inner_left]
    have hc : T (T.adjoint f) = kernelOperator (fun i i' => ∑ j, K i j * K i' j) f := by
      rw [show T = kernelOperator K from rfl, kernelOperator_adjoint,
        ← LinearMap.comp_apply, kernelOperator_comp]
    rw [hc]
    apply nonnegative_symmetric_kernel_quadratic_bound
    · intro i i'; exact Finset.sum_nonneg (fun j _ => mul_nonneg (hK i j) (hK i' j))
    · intro i i'; simp only [mul_comm]
    · exact hrow
  have hn : ‖T.adjoint.toContinuousLinearMap‖ ≤ Real.sqrt p := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg p)
    intro f
    change ‖T.adjoint f‖ ≤ Real.sqrt p * ‖f‖
    have hh := hq f
    have hs : (Real.sqrt p * ‖f‖) ^ 2 = p * ‖f‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hp]
    nlinarith [norm_nonneg (T.adjoint f), norm_nonneg f,
      mul_nonneg (Real.sqrt_nonneg p) (norm_nonneg f)]
  rw [LinearMap.adjoint_toContinuousLinearMap, LinearIsometryEquiv.norm_map] at hn
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hp)

end SignedSweeps
end

end OAI
