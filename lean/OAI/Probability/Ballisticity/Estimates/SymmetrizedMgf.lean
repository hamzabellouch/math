import Mathlib
import OAI.Probability.Ballisticity.Estimates.DifferentiableExp

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma symmetrized_mgf (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    mgf (fun p : ℝ × ℝ => p.1-p.2) (μ.prod μ) t = mgf id μ t*mgf id μ (-t) := by
  simp only [mgf,mul_sub,Real.exp_sub,Real.exp_neg,neg_mul,id_eq,div_eq_mul_inv]
  exact integral_prod_mul (fun x : ℝ => Real.exp (t*x)) (fun y : ℝ => (Real.exp (t*y))⁻¹)

lemma symmetrized_complexMGF (μ : Measure ℝ) [IsProbabilityMeasure μ] (z : ℂ) :
    complexMGF (fun p : ℝ × ℝ => p.1-p.2) (μ.prod μ) z =
      complexMGF id μ z*complexMGF id μ (-z) := by
  simp only [complexMGF,Complex.ofReal_sub,mul_sub,Complex.exp_sub,Complex.exp_neg,neg_mul,
    id_eq,div_eq_mul_inv]
  exact integral_prod_mul (fun x : ℝ => Complex.exp (z*x)) (fun y : ℝ => (Complex.exp (z*y))⁻¹)

lemma iid_difference_gaussian_mgf_product (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : ℝ≥0) (hv : (μ.prod μ).map (fun p : ℝ × ℝ => p.1-p.2) = gaussianReal 0 v) (t : ℝ) :
    mgf id μ t*mgf id μ (-t) = Real.exp (v*t^2/2) := by
  rw [← symmetrized_mgf,mgf_gaussianReal ⟨by fun_prop, hv⟩]
  simp

lemma iid_difference_gaussian_integrableExpSet (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : ℝ≥0) (hv : (μ.prod μ).map (fun p : ℝ × ℝ => p.1-p.2) = gaussianReal 0 v) :
    integrableExpSet id μ = Set.univ := by
  ext t
  simp only [Set.mem_univ,iff_true,integrableExpSet,Set.mem_ofPred_eq]
  apply mgf_pos_iff.mp
  have h := iid_difference_gaussian_mgf_product μ v hv t
  have hh : 0 < mgf id μ t*mgf id μ (-t) := by rw [h]; exact Real.exp_pos _
  exact pos_of_mul_pos_left hh mgf_nonneg

lemma exp_mean_le_mgf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : integrableExpSet id μ = Set.univ) (t : ℝ) :
    Real.exp (t*∫ x, x ∂μ) ≤ mgf id μ t := by
  have hi : Integrable id μ := integrable_of_mem_interior_integrableExpSet (by simp [hμ])
  have he : Integrable (fun x : ℝ => Real.exp (t*x)) μ := by
    have h : t ∈ integrableExpSet id μ := by rw [hμ]; trivial
    exact h
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun x : ℝ => Set.mem_univ (t*x)) (hi.const_mul t) he
  convert! h using 1
  congr 1
  exact (integral_const_mul t (id : ℝ → ℝ)).symm

lemma iid_difference_gaussian_mgf_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : ℝ≥0) (hv : (μ.prod μ).map (fun p : ℝ × ℝ => p.1-p.2) = gaussianReal 0 v)
    (t : ℝ) : mgf id μ t ≤ Real.exp (t*(∫ x, x ∂μ)+v*t^2/2) := by
  have h := exp_mean_le_mgf μ (iid_difference_gaussian_integrableExpSet μ v hv) (-t)
  have hp := iid_difference_gaussian_mgf_product μ v hv t
  have hb := mul_le_mul_of_nonneg_left h (mgf_nonneg (X := id) (μ := μ) (t := t))
  rw [hp] at hb
  have he : Real.exp (t*(∫ x,x ∂μ)+v*t^2/2)*Real.exp (-t*(∫ x,x ∂μ)) =
      Real.exp (v*t^2/2) := by rw [← Real.exp_add]; congr 1; ring
  rw [← he] at hb
  exact (mul_le_mul_iff_left₀ (Real.exp_pos _)).mp hb

theorem iid_difference_gaussian (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : ℝ≥0) (hv : (μ.prod μ).map (fun p : ℝ × ℝ => p.1-p.2) = gaussianReal 0 v) :
    μ = gaussianReal (∫ x, x ∂μ) (v/2) := by
  have hset := iid_difference_gaussian_integrableExpSet μ v hv
  have hz (z : ℂ) : z.re ∈ interior (integrableExpSet id μ) := by simp [hset]
  have hf : Differentiable ℂ (complexMGF id μ) :=
    fun z => (hasDerivAt_complexMGF (hz z)).differentiableAt
  have h0 : complexMGF id μ 0 = 1 := by simp [complexMGF]
  have hp (z : ℂ) : complexMGF id μ z*complexMGF id μ (-z) =
      Complex.exp ((v:ℂ)/2*z^2) := by
    rw [← symmetrized_complexMGF,complexMGF_gaussianReal ⟨by fun_prop, hv⟩]
    congr 1
    simp only [Complex.ofReal_zero,mul_zero,zero_add]
    ring
  let m := ∫ x, x ∂μ
  let C := |m|+(v:ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hb (z : ℂ) : ‖complexMGF id μ z‖ ≤ Real.exp (C*(1+‖z‖^2)) := by
    refine norm_complexMGF_le_mgf.trans ((iid_difference_gaussian_mgf_bound μ v hv z.re).trans ?_)
    apply Real.exp_le_exp.mpr
    have hm : z.re*m ≤ |m| *‖z‖ := by
      calc z.re*m ≤ |z.re*m| := le_abs_self _
        _ = |m| *|z.re| := by rw [abs_mul]; ring
        _ ≤ |m| *‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg m)
    have hs : z.re^2 ≤ ‖z‖^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z.re) (Complex.abs_re_le_norm z) 2
    have ht : ‖z‖ ≤ 1+‖z‖^2 := by nlinarith [sq_nonneg (‖z‖-1)]
    have hmv := mul_le_mul_of_nonneg_left ht (abs_nonneg m)
    have hvz := mul_le_mul_of_nonneg_left hs v.2
    have hv0 := mul_nonneg v.2 (sq_nonneg ‖z‖)
    dsimp [C,m] at *
    nlinarith [norm_nonneg z,abs_nonneg (∫ x,x ∂μ)]
  have hfac := entire_gaussian_factor hf h0 ((v:ℂ)/2) hp hC hb
  have hd : deriv (complexMGF id μ) 0 = (∫ x, x ∂μ : ℝ) := by
    calc
      _ = ∫ x : ℝ, (x : ℂ) ∂μ := by
        simpa only [id_eq,zero_mul,Complex.exp_zero,mul_one] using
          (hasDerivAt_complexMGF (hz 0)).deriv
      _ = _ := integral_complex_ofReal
  apply Measure.ext_of_complexMGF_id_eq
  funext z
  rw [hfac z,complexMGF_id_gaussianReal,hd]
  congr 1
  push_cast
  ring

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma map_iid_difference_linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    (μ : Measure E) [IsProbabilityMeasure μ] (L : E →L[ℝ] F) :
    ((μ.map L).prod (μ.map L)).map (fun p : F × F => p.1-p.2) =
      ((μ.prod μ).map (fun p : E × E => p.1-p.2)).map L := by
  rw [Measure.map_prod_map μ μ L.measurable L.measurable,
    Measure.map_map (show Measurable (fun p : F × F => p.1-p.2) by fun_prop)
      (L.measurable.prodMap L.measurable),
    Measure.map_map L.measurable (show Measurable (fun p : E × E => p.1-p.2) by fun_prop)]
  congr 1
  funext p
  exact (L.map_sub p.1 p.2).symm

theorem iid_difference_isGaussian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsGaussian ν]
    (hmean : ∫ x, x ∂ν = 0)
    (hv : (μ.prod μ).map (fun p : E × E => p.1-p.2) = ν) : IsGaussian μ := by
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  have hn : ν.map L = gaussianReal 0 (Var[L; ν]).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal,IsGaussian.integral_dual,hmean,map_zero]
  have hd : ((μ.map L).prod (μ.map L)).map (fun p : ℝ × ℝ => p.1-p.2) =
      gaussianReal 0 (Var[L; ν]).toNNReal := by
    rw [map_iid_difference_linear,hv,hn]
  exact ⟨∫ x, x ∂μ.map L,(Var[L; ν]).toNNReal/2,iid_difference_gaussian _ _ hd⟩

lemma iid_difference_gaussian_centered_linear {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E] (μ ν : Measure E) [IsProbabilityMeasure μ] [IsGaussian ν]
    (hmean : ∫ x, x ∂ν = 0)
    (hv : (μ.prod μ).map (fun p : E × E => p.1-p.2) = ν) (L : E →L[ℝ] ℝ) :
    μ.map (fun x => L (x-∫ y, y ∂μ)) = gaussianReal 0 ((Var[L; ν]).toNNReal/2) := by
  have : IsGaussian μ := iid_difference_isGaussian μ ν hmean hv
  have hn : ν.map L = gaussianReal 0 (Var[L; ν]).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal,IsGaussian.integral_dual,hmean,map_zero]
  have hd : ((μ.map L).prod (μ.map L)).map (fun p : ℝ × ℝ => p.1-p.2) =
      gaussianReal 0 (Var[L; ν]).toNNReal := by rw [map_iid_difference_linear,hv,hn]
  have hg := iid_difference_gaussian (μ.map L) _ hd
  have hi : (∫ x, x ∂μ.map L) = L (∫ x, x ∂μ) := by
    rw [integral_map L.measurable.aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => x) (μ.map L) from measurable_id.aestronglyMeasurable)]
    exact IsGaussian.integral_dual L
  have he : (fun x => L (x-∫ y, y ∂μ)) = (fun x : ℝ => x-L (∫ y, y ∂μ)) ∘ L := by
    funext x; simp
  rw [he,← Measure.map_map (by fun_prop) L.measurable,hg,hi]
  simpa only [sub_self] using (gaussianReal_map_sub_const (μ := L (∫ y, y ∂μ))
    (v := (Var[L; ν]).toNNReal/2) (L (∫ y, y ∂μ)))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
