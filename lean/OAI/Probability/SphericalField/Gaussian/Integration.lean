import Mathlib
import OAI.Probability.SphericalField.Poisson.WeightedTotal

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace

namespace SphericalPerceptron
def gaussianRotation (t : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((Real.cos t • ContinuousLinearMap.fst ℝ ℝ ℝ +
    Real.sin t • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (-Real.sin t • ContinuousLinearMap.fst ℝ ℝ ℝ +
      Real.cos t • ContinuousLinearMap.snd ℝ ℝ ℝ))

lemma gaussianRotation_apply (t : ℝ) (p : ℝ × ℝ) :
    gaussianRotation t p = (Real.cos t*p.1+Real.sin t*p.2,
      -Real.sin t*p.1+Real.cos t*p.2) := rfl

lemma gaussianRotation_preserving (t : ℝ) :
    MeasurePreserving (gaussianRotation t) ((gaussianReal 0 1).prod (gaussianReal 0 1))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  refine ⟨by fun_prop, Measure.ext_of_charFunDual ?_⟩
  ext L
  rw [charFunDual_map]
  simp only [charFunDual_prod, charFunDual_standardGaussian]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hL (x y : ℝ) : L (x,y) = x*L (1,0)+y*L (0,1) := by
    have he : (x,y) = x • (1,0) + y • (0,1) := by ext <;> simp
    rw [he,map_add,map_smul,map_smul]
    rfl
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply,gaussianRotation_apply,mul_one,mul_zero,zero_add,add_zero]
  rw [hL (Real.cos t) (-Real.sin t),hL (Real.sin t) (Real.cos t)]
  have h := Real.sin_sq_add_cos_sq t
  have h' : (Real.sin t : ℂ)^2+(Real.cos t : ℂ)^2=1 := by exact_mod_cast h
  push_cast only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_neg]
  linear_combination -(L (1,0)^2+L (0,1)^2)/2*h'

lemma integral_sq_ge_sq_integral_div {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : MemLp f 2 μ) (hμ : 0 < μ.real univ) :
    (∫ x, f x ∂μ)^2 ≤ μ.real univ * ∫ x, (f x)^2 ∂μ := by
  let i := ∫ x, f x ∂μ
  let a := μ.real univ
  have hi := hf.integrable (by norm_num)
  have hi2 := hf.integrable_sq
  have he : (∫ x, (f x-i/a)^2 ∂μ) =
      (∫ x, (f x)^2 ∂μ)-2*(i/a)*i+a*(i/a)^2 := by
    calc
      _ = ∫ x, (f x)^2-(2*(i/a))*f x+(i/a)^2 ∂μ := integral_congr_ae (ae_of_all _ fun x => by ring)
      _ = _ := by
        have ha := integral_add (hi2.sub (hi.const_mul (2*(i/a)))) (integrable_const ((i/a)^2))
        have hb := integral_sub hi2 (hi.const_mul (2*(i/a)))
        simp only [Pi.sub_apply] at ha
        rw [ha,hb,integral_const_mul,integral_const]
        rfl
  have hn : (0 : ℝ) ≤ ∫ x, (f x-i/a)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  rw [he] at hn
  have ha : a ≠ 0 := hμ.ne'
  have hae : a*(i/a)^2 = i^2/a := by field_simp
  have hie : 2*(i/a)*i = 2*(i^2/a) := by ring
  rw [hae,hie] at hn
  have : i^2/a ≤ ∫ x, (f x)^2 ∂μ := by linarith
  exact (div_le_iff₀ hμ).mp this |>.trans_eq (mul_comm ..)

lemma gaussian_rotation_path_bound {F D : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (D x) x)
    (hD : Continuous D) (x y : ℝ) :
    (F y-F x)^2 ≤ (Real.pi/2) * ∫ t in Ioc 0 (Real.pi/2),
      (D (Real.cos t*x+Real.sin t*y)*(-Real.sin t*x+Real.cos t*y))^2 := by
  let d := fun t => D (Real.cos t*x+Real.sin t*y)*(-Real.sin t*x+Real.cos t*y)
  have hd : Continuous d := by dsimp [d]; fun_prop
  have hdF (t : ℝ) : HasDerivAt (fun t => F (Real.cos t*x+Real.sin t*y)) (d t) t := by
    exact (hF _).comp t (((Real.hasDerivAt_cos t).mul_const x).add
      ((Real.hasDerivAt_sin t).mul_const y))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hdF t) (hd.intervalIntegrable 0 (Real.pi/2))
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,Real.cos_zero,Real.sin_zero,
    zero_mul,one_mul,zero_add,add_zero] at hi
  rw [intervalIntegral.integral_of_le (by positivity)] at hi
  have hm : MemLp d 2 (volume.restrict (Ioc 0 (Real.pi/2))) :=
    (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mpr
      ((hd.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hmass : (volume.restrict (Ioc 0 (Real.pi/2))).real univ = Real.pi/2 := by
    simp [Measure.real,Real.volume_Ioc]; positivity
  have hh := integral_sq_ge_sq_integral_div (volume.restrict (Ioc 0 (Real.pi/2))) hm
    (by rw [hmass]; positivity)
  rwa [hmass,hi] at hh

lemma standardGaussian_secondMoment : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
  simpa only [variance_id_gaussianReal,NNReal.coe_one,Pi.pow_apply,id_eq,
    integral_id_gaussianReal,zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero] using h.symm

lemma hasDerivAt_bounded_memLp {F D : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (D x) x)
    {C : ℝ} (hC : 0 ≤ C) (hDC : ∀ x, |D x| ≤ C) :
    MemLp F 2 (gaussianReal 0 1) := by
  have hL : LipschitzWith ⟨C,hC⟩ F := lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hF x).differentiableAt) (fun x => by
      rw [(hF x).deriv]
      exact_mod_cast hDC x)
  have hgc : LipschitzWith ⟨C,hC⟩ (fun x => F x-F 0) := by
    intro x y
    simpa only [edist_sub_right] using hL x y
  have hg := hgc.comp_memLp (by simp) (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
  have hh := hg.add (memLp_const (F 0))
  have he : ((fun x => F x-F 0) ∘ id + fun _ => F 0) = F := by
    funext x
    simp
  rw [he] at hh
  convert! hh

lemma gaussian_rotation_derivative_square_mean {D : ℝ → ℝ}
    (hD : Continuous D) (t : ℝ) :
    (∫ p : ℝ × ℝ,
      (D (Real.cos t*p.1+Real.sin t*p.2)*(-Real.sin t*p.1+Real.cos t*p.2))^2
      ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫ x, (D x)^2 ∂gaussianReal 0 1 := by
  have he := integral_map (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
    (gaussianRotation t).continuous.measurable.aemeasurable
    (f := fun p : ℝ×ℝ => (D p.1*p.2)^2) (by fun_prop)
  rw [(gaussianRotation_preserving t).map_eq] at he
  dsimp only [gaussianRotation_apply] at he
  rw [← he]
  simp_rw [mul_pow]
  rw [integral_prod_mul (fun x : ℝ => (D x)^2) (fun y : ℝ => y^2),standardGaussian_secondMoment,mul_one]

lemma integral_independent_difference_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) :
    (∫ p : Ω×Ω, (F p.1-F p.2)^2 ∂μ.prod μ) = 2*variance F μ := by
  have hi := hF.integrable (by norm_num)
  have hi2 := hF.integrable_sq
  have hprod := hi.mul_prod hi
  calc
    _ = ∫ p : Ω×Ω, (F p.1)^2-2*(F p.1*F p.2)+(F p.2)^2 ∂μ.prod μ :=
      integral_congr_ae (ae_of_all _ fun p => by ring)
    _ = _ := by
      have ha := integral_add ((hi2.comp_fst μ).sub (hprod.const_mul 2)) (hi2.comp_snd μ)
      have hb := integral_sub (hi2.comp_fst μ) (hprod.const_mul 2)
      simp only [Pi.sub_apply] at ha
      rw [ha,hb,integral_const_mul,integral_fun_fst (fun x : Ω => (F x)^2),
        integral_fun_snd (fun x : Ω => (F x)^2),
        integral_prod_mul F F,variance_eq_sub hF]
      simp only [probReal_univ,one_smul,Pi.pow_apply]
      ring

end SphericalPerceptron
end
end
end

end OAI
