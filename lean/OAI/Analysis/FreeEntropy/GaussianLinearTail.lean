import OAI.Analysis.FreeEntropy.MicrostatesSelection

namespace OAI

universe u1

noncomputable section
open scoped NNReal
open MeasureTheory ProbabilityTheory Finset Set
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 def gaussianLinear (c : ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i, c i*x i
 theorem gaussianLinear_exp_eq (c : ι → ℝ) (t : ℝ) :
    (fun x => Real.exp (t*gaussianLinear c x)) = fun x => ∏ i, Real.exp ((t*c i)*x i) := by
  funext x
  rw [← Real.exp_sum]
  congr 1
  simp [gaussianLinear, mul_sum, mul_assoc]
 theorem gaussianLinear_exp_integrable (c : ι → ℝ) (t : ℝ) :
    Integrable (fun x => Real.exp (t*gaussianLinear c x)) (productGaussian ι) := by
  rw [gaussianLinear_exp_eq]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (t*c i))
 theorem gaussianLinear_mgf (c : ι → ℝ) (t : ℝ) :
    mgf (gaussianLinear c) (productGaussian ι) t = Real.exp ((∑ i, c i^2)*t^2/2) := by
  unfold mgf
  rw [gaussianLinear_exp_eq]
  unfold productGaussian
  rw [integral_fintype_prod_eq_prod (fun i s => Real.exp ((t*c i)*s))]
  have hi (i : ι) : (∫ s, Real.exp ((t*c i)*s) ∂gaussianReal 0 1) = Real.exp ((t*c i)^2/2) := by
    simpa only [mgf, NNReal.coe_one, zero_mul, zero_add, one_mul] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (t*c i)
  simp_rw [hi]
  rw [← Real.exp_sum]
  congr 1
  simp [mul_pow, sum_div, sum_mul]
  ring_nf
 theorem gaussianLinear_subgaussian (c : ι → ℝ) (K : ℝ≥0) (hK : (∑ i, c i^2) ≤ K) :
    HasSubgaussianMGF (gaussianLinear c) K (productGaussian ι) where
  integrable_exp_mul := gaussianLinear_exp_integrable c
  mgf_le t := by rw [gaussianLinear_mgf]; apply Real.exp_le_exp.mpr; gcongr
 theorem gaussianLinear_tail (c : ι → ℝ) (K : ℝ≥0) (hK : (∑ i, c i^2) ≤ K) {u : ℝ} (hu : 0 ≤ u) :
    (productGaussian ι).real {x | u ≤ |gaussianLinear c x|} ≤ 2*Real.exp (-u^2/(2*K)) := by
  have h := gaussianLinear_subgaussian c K hK
  have hp := h.measure_ge_le hu
  have hm := h.neg.measure_ge_le hu
  have he : {x | u ≤ |gaussianLinear c x|} = {x | u ≤ gaussianLinear c x} ∪ {x | u ≤ -gaussianLinear c x} := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_union]; exact le_abs
  rw [he]
  calc
    _ ≤ (productGaussian ι).real {x | u ≤ gaussianLinear c x} + (productGaussian ι).real {x | u ≤ -gaussianLinear c x} := measureReal_union_le _ _
    _ ≤ _ := by simpa only [Pi.neg_apply] using add_le_add hp hm |>.trans_eq (two_mul _).symm
end FiniteEntropySeparation

end

end OAI
