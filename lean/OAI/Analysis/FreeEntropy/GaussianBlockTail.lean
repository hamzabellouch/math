import OAI.Analysis.FreeEntropy.NormalLaw

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem normalLaw_rotation (s : ℝ) (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (normalLaw s).map U = normalLaw s := by
  have he : (fun x => ENNReal.ofReal (normalKernel s x)) =
      (fun x => ENNReal.ofReal (normalKernel s x)) ∘ U := by
    funext x
    simp [normalKernel]
  unfold normalLaw
  conv_lhs => rw [he]
  exact map_withDensity_of_measurePreserving U.measurePreserving _
    (ENNReal.measurable_ofReal.comp (normalKernel_continuous_space s).measurable)
 theorem normalLaw_measurePreserving (s : ℝ) (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    MeasurePreserving U (normalLaw s) (normalLaw s) :=
  ⟨U.continuous.measurable,normalLaw_rotation s U⟩
 theorem squareExp_density (x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (x^2/4) =
      (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(1/4:ℝ)*x^2) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,mul_assoc,← Real.exp_add]
  congr 2
  ring
 theorem squareExp_integrable : Integrable (fun x : ℝ => Real.exp (x^2/4)) (gaussianReal 0 1) := by
  rw [gaussian_weight_integrable one_ne_zero]
  simp only [smul_eq_mul,squareExp_density]
  exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/4)).const_mul _
 theorem squareExp_integral : (∫x : ℝ,Real.exp (x^2/4) ∂gaussianReal 0 1) = Real.sqrt 2 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul,squareExp_density]
  rw [integral_const_mul,integral_gaussian]
  have hp := Real.pi_pos
  have he : Real.pi / (1/4:ℝ)=4*Real.pi := by ring
  rw [he,Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
  norm_num
  have hs : Real.sqrt Real.pi≠0 := (Real.sqrt_pos.mpr hp).ne'
  have h2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
 theorem masked_exp_integrable (m : Finset ι) :
    Integrable (fun x : ι → ℝ => Real.exp ((∑i∈m,x i^2)/4)) (productGaussian ι) := by
  classical
  have he : (fun x : ι → ℝ => Real.exp ((∑i∈m,x i^2)/4)) =
      fun x => ∏i,if i∈m then Real.exp (x i^2/4) else 1 := by
    funext x
    rw [sum_div,Real.exp_sum]
    simp
  rw [he]
  apply Integrable.fintype_prod (f := fun i (x:ℝ) => if i∈m then Real.exp (x^2/4) else 1)
  intro i
  by_cases hi : i∈m
  · simpa [hi] using squareExp_integrable
  · simp [hi]
 theorem masked_exp_integral (m : Finset ι) :
    (∫x : ι → ℝ,Real.exp ((∑i∈m,x i^2)/4) ∂productGaussian ι) = Real.sqrt 2^m.card := by
  classical
  have he : (fun x : ι → ℝ => Real.exp ((∑i∈m,x i^2)/4)) =
      fun x => ∏i,if i∈m then Real.exp (x i^2/4) else 1 := by
    funext x
    rw [sum_div,Real.exp_sum]
    simp
  rw [he,productGaussian,integral_fintype_prod_eq_prod (fun i (x:ℝ) => if i∈m then Real.exp (x^2/4) else 1)]
  have hh i : (∫x : ℝ,if i∈m then Real.exp (x^2/4) else 1 ∂gaussianReal 0 1)=
      if i∈m then Real.sqrt 2 else 1 := by
    by_cases hi : i∈m <;> simp [hi,squareExp_integral]
  simp_rw [hh]
  simp
 theorem masked_square_tail (m : Finset ι) (u : ℝ) :
    (productGaussian ι) {x | u≤∑i∈m,x i^2} ≤
      ENNReal.ofReal (Real.exp (-u/4)*Real.sqrt 2^m.card) := by
  have hi := (masked_exp_integrable m).const_mul (Real.exp (-u/4))
  have hh := hi.measure_le_integral (Filter.Eventually.of_forall (fun x => by positivity))
    (s := {x | u≤∑i∈m,x i^2}) (fun x hx => by
      rw [← Real.exp_add,Real.one_le_exp_iff]
      dsimp at hx
      linarith)
  rw [integral_const_mul,masked_exp_integral] at hh
  exact hh
 theorem normalLaw_mask_tail (m : Finset ι) {s : ℝ} (hs : 0<s) (u : ℝ) :
    (normalLaw s) {x | u≤∑i∈m,x i^2} ≤
      ENNReal.ofReal (Real.exp (-u/(4*s))*Real.sqrt 2^m.card) := by
  classical
  rw [normalLaw_eq_scaled hs,Measure.map_apply (by fun_prop) (isClosed_le continuous_const (by fun_prop)).measurableSet]
  have he : (fun x : ι → ℝ => Real.sqrt s • WithLp.toLp 2 x) ⁻¹' {x : EuclideanSpace ℝ ι | u≤∑i∈m,x i^2} =
      {x | u/s≤∑i∈m,x i^2} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,PiLp.smul_apply,smul_eq_mul,mul_pow,Real.sq_sqrt hs.le,← mul_sum]
    rw [div_le_iff₀ hs,mul_comm]
  rw [he]
  convert masked_square_tail m (u/s) using 1 ; congr 2 ; ring_nf
 theorem gaussian_square_integral : (∫x : ℝ,x^2 ∂gaussianReal 0 1)=1 := by
  simpa [pow_two] using gaussian_polynomial_stein (Polynomial.X : Polynomial ℝ)
end FiniteEntropySeparation

end

end OAI
