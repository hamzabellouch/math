import OAI.Analysis.FreeEntropy.GUEStein

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Classical Topology
namespace FiniteEntropySeparation
 theorem complex_polynomial_covariance {ι : Type u1} [Fintype ι] [DecidableEq ι]
    {f g : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (hg : IsComplexPolynomial g) :
    ‖(∫ x, f x*g x ∂productGaussian ι)-(∫ x, f x ∂productGaussian ι)*(∫ x, g x ∂productGaussian ι)‖ ≤
      ((∫ x, ‖f x-∫ y, f y ∂productGaussian ι‖^2 ∂productGaussian ι)+
        (∫ x, ‖g x-∫ y, g y ∂productGaussian ι‖^2 ∂productGaussian ι))/2 := by
  let a := ∫ x, f x ∂productGaussian ι
  let b := ∫ x, g x ∂productGaussian ι
  have hf' := hf.sub (IsComplexPolynomial.const a)
  have hg' := hg.sub (IsComplexPolynomial.const b)
  have he : (∫ x, (f x-a)*(g x-b) ∂productGaussian ι) = (∫ x, f x*g x ∂productGaussian ι)-a*b := by
    have heq : (fun x => (f x-a)*(g x-b)) = fun x => f x*g x-f x*b-a*g x+a*b := by funext x; ring
    rw [heq, integral_add ((hf.mul hg).sub (hf.mul_const b) |>.sub (hg.const_mul a)).integrable (integrable_const _),
      integral_sub ((hf.mul hg).sub (hf.mul_const b)).integrable (hg.const_mul a).integrable,
      integral_sub (hf.mul hg).integrable (hf.mul_const b).integrable,
      integral_mul_const, integral_const_mul]
    simp only [a,b,integral_const,probReal_univ,one_smul]
    ring
  rw [← he]
  calc
    _ ≤ ∫ x, ‖(f x-a)*(g x-b)‖ ∂productGaussian ι := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (‖f x-a‖^2+‖g x-b‖^2)/2 ∂productGaussian ι := by
      apply integral_mono (hf'.mul hg').integrable.norm (((hf'.norm_sq).add (hg'.norm_sq)).integrable.div_const 2)
      intro x
      dsimp only
      rw [norm_mul]
      nlinarith [sq_nonneg (‖f x-a‖-‖g x-b‖)]
    _ = _ := by rw [integral_div, integral_add hf'.norm_sq.integrable hg'.norm_sq.integrable]
 theorem matrixTraceWord_covariance_bound {α : Type u2} {n d : ℕ} (hd : 0 < d)
    (A : α → Matrix (Fin d) (Fin d) ℂ) {R : ℝ} (hR : 0 ≤ R) (hA : ∀ a, matrixOpNorm (A a) ≤ R)
    (u v : List (α ⊕ Fin n)) :
    ‖(∫ x, matrixTraceWord (jointMatrix A x) u*matrixTraceWord (jointMatrix A x) v ∂productGaussian (MatrixIndex n d))-
      (∫ x, matrixTraceWord (jointMatrix A x) u ∂productGaussian (MatrixIndex n d))*(∫ x, matrixTraceWord (jointMatrix A x) v ∂productGaussian (MatrixIndex n d))‖ ≤
      ((u.length:ℝ)^2*jointMomentBound n R (2*(u.length-1))+(v.length:ℝ)^2*jointMomentBound n R (2*(v.length-1)))/(2*(d:ℝ)^2) := by
  have h := complex_polynomial_covariance (matrixTraceWord_polynomial A u) (matrixTraceWord_polynomial A v)
  have hu := matrixTraceWord_variance_bound hd A hR hA u
  have hv := matrixTraceWord_variance_bound hd A hR hA v
  calc
    _ ≤ _ := h
    _ ≤ (((u.length:ℝ)^2/(d:ℝ)^2)*jointMomentBound n R (2*(u.length-1))+((v.length:ℝ)^2/(d:ℝ)^2)*jointMomentBound n R (2*(v.length-1)))/2 := by linarith
    _ = _ := by ring
 theorem tendsto_zero_of_norm_bound_inv_sq {D : ℕ → ℕ} (hD : Tendsto D atTop atTop)
    {f : ℕ → ℂ} {C : ℝ} (hf : ∀ k, ‖f k‖ ≤ C/(D k:ℝ)^2) : Tendsto f atTop (𝓝 0) := by
  have ht : Tendsto (fun k => C/(D k:ℝ)^2) atTop (𝓝 0) := by
    have hc : Tendsto (fun k => (D k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hD
    have hi := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0) |>.comp hc)
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hi
  exact squeeze_zero_norm hf ht
end FiniteEntropySeparation

end

end OAI
