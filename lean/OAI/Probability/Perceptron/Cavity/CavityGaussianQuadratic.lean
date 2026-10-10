import Mathlib
import OAI.Probability.Perceptron.Variational.PiMarkLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

def squareGaussianVariance : ℝ := variance (fun y : ℝ=>y^2) (gaussianReal 0 1)

lemma squareGaussianVariance_nonneg : 0 ≤ squareGaussianVariance := variance_nonneg _ _

lemma gaussian_square_variance_scale (r : ℝ≥0) :
    variance (fun y : ℝ=>y^2) (gaussianReal 0 r)=(r:ℝ)^2*squareGaussianVariance := by
  have hg : (gaussianReal 0 1).map (fun y : ℝ=>Real.sqrt (r:ℝ)*y)=gaussianReal 0 r := by
    convert gaussianReal_map_const_mul (μ:=0) (v:=1) (Real.sqrt (r:ℝ)) using 1
    simp only [mul_zero,mul_one]
    congr 1
    exact NNReal.coe_injective (Real.sq_sqrt r.coe_nonneg).symm
  rw [←hg,variance_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def,mul_pow,Real.sq_sqrt r.coe_nonneg]
  exact variance_const_mul (r:ℝ) (fun y : ℝ=>y^2) _

def cavityQuadraticScalar (M : ℕ) (a : Fin M→ℝ) (t : ℝ) (r : ℝ≥0) (y : Fin M→ℝ) : ℝ :=
  t*∑ i,a i*((y i)^2-r)

lemma cavityQuadraticScalar_memLp (M : ℕ) (a : Fin M→ℝ) (t : ℝ) (r : ℝ≥0) :
    MemLp (cavityQuadraticScalar M a t r) 2 (Measure.pi (fun _=>gaussianReal 0 r)) := by
  exact (memLp_finsetSum _ (fun i _=>
    (((gaussian_square_memLp_two r).comp_measurePreserving (measurePreserving_eval _ i)).sub
      (memLp_const (r:ℝ))).const_mul (a i))).const_mul t

lemma cavityQuadraticScalar_mean (M : ℕ) (a : Fin M→ℝ) (t : ℝ) (r : ℝ≥0) :
    (∫ y,cavityQuadraticScalar M a t r y ∂Measure.pi (fun _=>gaussianReal 0 r))=0 := by
  unfold cavityQuadraticScalar
  rw [integral_const_mul,integral_finsetSum]
  · have he i : (∫ y : Fin M→ℝ,a i*((y i)^2-r) ∂Measure.pi (fun _=>gaussianReal 0 r))=0 := by
      rw [integral_const_mul,integral_comp_eval (μ:=fun _ : Fin M=>gaussianReal 0 r) (i:=i) (f:=fun y : ℝ=>y^2-r) (by fun_prop)]
      rw [integral_sub ((gaussian_square_memLp_two r).integrable (by norm_num)) (integrable_const _),gaussian_square_mean]
      simp
    simp_rw [he]
    simp
  · intro i _
    exact ((((gaussian_square_memLp_two r).comp_measurePreserving (measurePreserving_eval _ i)).sub
      (memLp_const (r:ℝ))).const_mul (a i)).integrable (by norm_num)

lemma cavityQuadraticScalar_second_moment (M : ℕ) (a : Fin M→ℝ) (t : ℝ) (r : ℝ≥0) :
    (∫ y,(cavityQuadraticScalar M a t r y)^2 ∂Measure.pi (fun _=>gaussianReal 0 r))=
      t^2*(r:ℝ)^2*squareGaussianVariance*∑ i,(a i)^2 := by
  have hv := variance_eq_sub (cavityQuadraticScalar_memLp M a t r)
  rw [cavityQuadraticScalar_mean] at hv
  simp only [Pi.pow_apply,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] at hv
  rw [←hv]
  unfold cavityQuadraticScalar
  rw [variance_const_mul]
  have hs := variance_sum_pi (μ:=fun _ : Fin M=>gaussianReal 0 r)
    (X:=fun i y=>a i*(y^2-r)) (fun i=>((gaussian_square_memLp_two r).sub (memLp_const (r:ℝ))).const_mul (a i))
  have he : (∑ i : Fin M,fun y : Fin M→ℝ=>a i*((y i)^2-r))=(fun y=>∑ i,a i*((y i)^2-r)) := by ext y; simp
  rw [he] at hs
  rw [hs]
  simp_rw [variance_const_mul,variance_sub_const (show AEStronglyMeasurable (fun y : ℝ=>y^2) (gaussianReal 0 r) from by fun_prop),gaussian_square_variance_scale]
  rw [←Finset.sum_mul]
  ring

lemma cavityQuadraticScalar_second_moment_bound (M : ℕ) (a : Fin M→ℝ) (t : ℝ) (r : ℝ≥0)
    {C : ℝ} (_hC : 0≤C) (ha : ∀ i,|a i|≤C) :
    (∫ y,(cavityQuadraticScalar M a t r y)^2 ∂Measure.pi (fun _=>gaussianReal 0 r))≤
      t^2*(r:ℝ)^2*squareGaussianVariance*M*C^2 := by
  rw [cavityQuadraticScalar_second_moment,mul_assoc _ (M:ℝ) (C^2)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) squareGaussianVariance_nonneg)
  calc
    (∑ i,(a i)^2)≤∑ _ : Fin M,C^2 := Finset.sum_le_sum fun i _=>by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (a i)) (ha i) 2
    _=M*C^2 := by simp

end SphericalPerceptronFreeEnergy
end

end OAI
