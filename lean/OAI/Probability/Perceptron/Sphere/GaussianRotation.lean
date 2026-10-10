import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy

lemma charFunDual_standardGaussian (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 1) L = Complex.exp (-(L 1 : ℂ)^2/2) := by
  have he : (L : ℝ → ℝ) = fun x => L 1*x := by
    funext x
    have h := L.map_smul x (1 : ℝ)
    simpa only [smul_eq_mul,mul_one,mul_comm x,one_mul] using h
  have hm : (∫ x : ℝ, L 1*x ∂gaussianReal 0 1) = 0 := by
    rw [integral_const_mul]
    simp
  have hv : variance (fun x : ℝ => L 1*x) (gaussianReal 0 1) = (L 1)^2 := by
    change variance (fun x : ℝ => L 1*id x) (gaussianReal 0 1) = _
    rw [variance_const_mul]
    simp [variance_id_gaussianReal]
  rw [IsGaussian.charFunDual_eq, integral_complex_ofReal, he, hm, hv]
  congr 1
  push_cast only [Complex.ofReal_zero,Complex.ofReal_pow]
  ring_nf

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

lemma standardGaussian_poincare {F D : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (D x) x)
    (hD : Continuous D) {C : ℝ} (hC : 0 ≤ C) (hDC : ∀ x, |D x| ≤ C) :
    variance F (gaussianReal 0 1) ≤ (Real.pi^2/8)*(∫ x, (D x)^2 ∂gaussianReal 0 1) := by
  let γ := gaussianReal 0 1
  let μ := γ.prod γ
  let T := Real.pi/2
  let ν := volume.restrict (Ioc 0 T)
  let d := fun (t : ℝ) (p : ℝ×ℝ) =>
    D (Real.cos t*p.1+Real.sin t*p.2)*(-Real.sin t*p.1+Real.cos t*p.2)
  have hT : 0 < T := by dsimp [T]; positivity
  have hν : ν.real univ = T := by simp [ν,Measure.real,Real.volume_Ioc,hT.le]
  have hdom (t : ℝ) (p : ℝ×ℝ) : (d t p)^2 ≤ 2*C^2*(p.1^2+p.2^2) := by
    have hb : |-Real.sin t*p.1+Real.cos t*p.2| ≤ |p.1|+|p.2| := by
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_mul,abs_neg]
      exact add_le_add (by nlinarith [Real.abs_sin_le_one t,abs_nonneg p.1])
        (by nlinarith [Real.abs_cos_le_one t,abs_nonneg p.2])
    have hb2 : (-Real.sin t*p.1+Real.cos t*p.2)^2 ≤ 2*(p.1^2+p.2^2) := by
      have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ |p.1|+|p.2|)).mpr hb
      simp only [sq_abs] at hh
      nlinarith [sq_nonneg (|p.1|-|p.2|),sq_abs p.1,sq_abs p.2]
    have hD2 : (D (Real.cos t*p.1+Real.sin t*p.2))^2 ≤ C^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hDC _)
    dsimp only [d]
    rw [mul_pow]
    have hh := mul_le_mul hD2 hb2 (sq_nonneg _) (sq_nonneg C)
    nlinarith
  have hs : Integrable (fun x : ℝ => x^2) γ := (memLp_id_gaussianReal 2).integrable_sq
  have hdI : Integrable (fun p : (ℝ×ℝ)×ℝ => (d p.2 p.1)^2) (μ.prod ν) := by
    have hh : Integrable (fun p : (ℝ×ℝ)×ℝ => 2*C^2*(p.1.1^2+p.1.2^2)) (μ.prod ν) :=
      (((hs.comp_fst γ).add (hs.comp_snd γ)).const_mul (2*C^2)).comp_fst ν
    apply hh.mono' (by dsimp [d]; fun_prop)
    exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,abs_sq] using hdom p.2 p.1
  have hmF : MemLp F 2 γ := hasDerivAt_bounded_memLp hF hC hDC
  have hdiff : Integrable (fun p : ℝ×ℝ => (F p.2-F p.1)^2) μ := by
    simpa only [Pi.sub_apply] using ((hmF.comp_snd γ).sub (hmF.comp_fst γ)).integrable_sq
  have he : (∫ p : ℝ×ℝ, (F p.2-F p.1)^2 ∂μ) = 2*variance F γ := by
    rw [show (fun p : ℝ×ℝ => (F p.2-F p.1)^2) = fun p => (F p.1-F p.2)^2 by
      funext p; ring]
    exact integral_independent_difference_square γ hmF
  have hn := integral_mono_ae hdiff (hdI.integral_prod_left.const_mul T)
    (ae_of_all _ fun p => gaussian_rotation_path_bound hF hD p.1 p.2)
  rw [he,integral_const_mul,← integral_prod _ hdI,integral_prod_symm _ hdI] at hn
  have hmeans : (∫ t, ∫ p : ℝ×ℝ, (d t p)^2 ∂μ ∂ν) =
      T*(∫ x, (D x)^2 ∂γ) := by
    simp_rw [show ∀ t, (∫ p : ℝ×ℝ, (d t p)^2 ∂μ) = ∫ x, (D x)^2 ∂γ
      from fun t => gaussian_rotation_derivative_square_mean hD t]
    rw [integral_const,hν,smul_eq_mul]
  rw [hmeans] at hn
  dsimp only [T] at hn
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma dual_rotation_norm (A B : StrongDual ℝ E) (t : ℝ) :
    ‖Real.cos t • A - Real.sin t • B‖^2 + ‖Real.sin t • A + Real.cos t • B‖^2 =
      ‖A‖^2+‖B‖^2 := by
  let e := (InnerProductSpace.toDual ℝ E).symm
  rw [← e.norm_map (Real.cos t • A - Real.sin t • B),
    ← e.norm_map (Real.sin t • A + Real.cos t • B),← e.norm_map A,← e.norm_map B]
  simp only [map_sub,map_add,map_smul,norm_sub_sq_real,norm_add_sq_real,
    real_inner_smul_left,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have h := Real.sin_sq_add_cos_sq t
  nlinarith [sq_nonneg ‖e A‖,sq_nonneg ‖e B‖]

def gaussianVectorRotation (t : ℝ) : (E × E) →L[ℝ] (E × E) :=
  ((Real.cos t • ContinuousLinearMap.fst ℝ E E +
    Real.sin t • ContinuousLinearMap.snd ℝ E E).prod
    (-Real.sin t • ContinuousLinearMap.fst ℝ E E +
      Real.cos t • ContinuousLinearMap.snd ℝ E E))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gaussianVectorRotation_apply (t : ℝ) (p : E×E) :
    gaussianVectorRotation t p = (Real.cos t • p.1+Real.sin t • p.2,
      -Real.sin t • p.1+Real.cos t • p.2) := rfl

lemma gaussianVectorRotation_preserving (t : ℝ) :
    MeasurePreserving (gaussianVectorRotation (E := E) t) ((stdGaussian E).prod (stdGaussian E))
      ((stdGaussian E).prod (stdGaussian E)) := by
  refine ⟨by fun_prop, Measure.ext_of_charFunDual ?_⟩
  ext L
  rw [charFunDual_map]
  simp only [charFunDual_prod,charFunDual_stdGaussian]
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  let A := L.comp (ContinuousLinearMap.inl ℝ E E)
  let B := L.comp (ContinuousLinearMap.inr ℝ E E)
  have hsplit (x y : E) : L (x,y) = L (x,0)+L (0,y) := by
    simpa using L.map_add (x,0) (0,y)
  have ha : (L.comp (gaussianVectorRotation t)).comp (ContinuousLinearMap.inl ℝ E E) =
      Real.cos t • A - Real.sin t • B := by
    ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
      smul_apply,sub_apply,gaussianVectorRotation_apply,smul_zero,add_zero]
    rw [hsplit]
    change A (Real.cos t • x) + B (-Real.sin t • x) = _
    simp [sub_eq_add_neg]
  have hb : (L.comp (gaussianVectorRotation t)).comp (ContinuousLinearMap.inr ℝ E E) =
      Real.sin t • A + Real.cos t • B := by
    ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
      smul_apply,add_apply,gaussianVectorRotation_apply,smul_zero,zero_add]
    rw [hsplit]
    change A (Real.sin t • x) + B (Real.cos t • x) = _
    simp
  rw [ha,hb]
  have h := dual_rotation_norm A B t
  have hc : (‖Real.cos t • A - Real.sin t • B‖ : ℂ)^2 +
    (‖Real.sin t • A + Real.cos t • B‖ : ℂ)^2 = (‖A‖ : ℂ)^2+(‖B‖ : ℂ)^2 := by
    exact_mod_cast h
  change _ = -(‖A‖ : ℂ)^2/2 + -(‖B‖ : ℂ)^2/2
  linear_combination -hc/2

lemma stdGaussian_dual_secondMoment (L : StrongDual ℝ E) :
    (∫ x, (L x)^2 ∂stdGaussian E) = ‖L‖^2 := by
  have hm : MemLp L 2 (stdGaussian E) := IsGaussian.memLp_dual _ _ 2 (by simp)
  have h := variance_eq_sub hm
  rw [integral_strongDual_stdGaussian,zero_pow (by omega),sub_zero,
    variance_dual_stdGaussian] at h
  exact h.symm

lemma hasFDerivAt_bounded_gaussian_memLp {F : E → ℝ} {D : E → StrongDual ℝ E}
    (hF : ∀ x, HasFDerivAt F (D x) x) {C : ℝ} (hC : 0 ≤ C)
    (hDC : ∀ x, ‖D x‖ ≤ C) : MemLp F 2 (stdGaussian E) := by
  have hL : LipschitzWith ⟨C,hC⟩ F := lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hF x).differentiableAt) (fun x => by
      rw [(hF x).fderiv]
      exact_mod_cast hDC x)
  have hgc : LipschitzWith ⟨C,hC⟩ (fun x => F x-F 0) := by
    intro x y
    simpa only [edist_sub_right] using hL x y
  have hg := hgc.comp_memLp (by simp) (IsGaussian.memLp_id (stdGaussian E) 2 (by simp))
  have hh := hg.add (memLp_const (F 0))
  have he : ((fun x => F x-F 0) ∘ id + fun _ => F 0) = F := by
    funext x
    simp
  rw [he] at hh
  convert! hh

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gaussian_vector_rotation_path_bound {F : E → ℝ} {D : E → StrongDual ℝ E}
    (hF : ∀ x, HasFDerivAt F (D x) x) (hD : Continuous D) (x y : E) :
    (F y-F x)^2 ≤ (Real.pi/2) * ∫ t in Ioc 0 (Real.pi/2),
      (D (Real.cos t • x+Real.sin t • y) (-Real.sin t • x+Real.cos t • y))^2 := by
  let d := fun t => D (Real.cos t • x+Real.sin t • y) (-Real.sin t • x+Real.cos t • y)
  have hd : Continuous d := by dsimp [d]; fun_prop
  have hdF (t : ℝ) : HasDerivAt (fun t => F (Real.cos t • x+Real.sin t • y)) (d t) t := by
    exact (hF _).comp_hasDerivAt t (((Real.hasDerivAt_cos t).smul_const x).add
      ((Real.hasDerivAt_sin t).smul_const y))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hdF t) (hd.intervalIntegrable 0 (Real.pi/2))
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,Real.cos_zero,Real.sin_zero,
    zero_smul,one_smul,zero_add,add_zero] at hi
  rw [intervalIntegral.integral_of_le (by positivity)] at hi
  have hm : MemLp d 2 (volume.restrict (Ioc 0 (Real.pi/2))) :=
    (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mpr
      ((hd.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hmass : (volume.restrict (Ioc 0 (Real.pi/2))).real univ = Real.pi/2 := by
    simp [Measure.real,Real.volume_Ioc]; positivity
  have hh := integral_sq_ge_sq_integral_div (volume.restrict (Ioc 0 (Real.pi/2)))
    hm (by rw [hmass]; positivity)
  rw [hmass,hi] at hh
  exact hh

lemma gaussian_vector_rotation_derivative_square_mean {D : E → StrongDual ℝ E}
    (hD : Continuous D) {C : ℝ} (hDC : ∀ x, ‖D x‖ ≤ C) (t : ℝ) :
    (∫ p : E × E,
      (D (Real.cos t • p.1+Real.sin t • p.2) (-Real.sin t • p.1+Real.cos t • p.2))^2
      ∂(stdGaussian E).prod (stdGaussian E)) =
      ∫ x, ‖D x‖^2 ∂stdGaussian E := by
  have he := integral_map (μ := (stdGaussian E).prod (stdGaussian E))
    (gaussianVectorRotation t).continuous.measurable.aemeasurable
    (f := fun p : E×E => (D p.1 p.2)^2) (by fun_prop)
  rw [(gaussianVectorRotation_preserving t).map_eq] at he
  dsimp only [gaussianVectorRotation_apply] at he
  rw [← he]
  have hi : Integrable (fun p : E×E => (D p.1 p.2)^2) ((stdGaussian E).prod (stdGaussian E)) := by
    have hh := ((IsGaussian.memLp_id (stdGaussian E) 2 (by simp)).norm.integrable_sq.const_mul (C^2)).comp_snd (stdGaussian E)
    apply hh.mono' (by fun_prop)
    refine ae_of_all _ fun p => ?_
    have hC : 0 ≤ C := (norm_nonneg (D p.1)).trans (hDC _)
    have hh : |D p.1 p.2| ≤ C*‖p.2‖ := (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hDC _) (norm_nonneg _))
    have hh2 := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (norm_nonneg p.2))).mpr hh
    simpa only [Real.norm_eq_abs,abs_sq,sq_abs,mul_pow,id_eq] using hh2
  rw [integral_prod _ hi]
  congr 1
  funext x
  exact stdGaussian_dual_secondMoment (D x)

lemma stdGaussian_poincare {F : E → ℝ} {D : E → StrongDual ℝ E}
    (hF : ∀ x, HasFDerivAt F (D x) x) (hD : Continuous D)
    {C : ℝ} (hC : 0 ≤ C) (hDC : ∀ x, ‖D x‖ ≤ C) :
    variance F (stdGaussian E) ≤ (Real.pi^2/8)*(∫ x, ‖D x‖^2 ∂stdGaussian E) := by
  let γ := stdGaussian E
  let μ := γ.prod γ
  let T := Real.pi/2
  let ν := volume.restrict (Ioc 0 T)
  let d := fun (t : ℝ) (p : E×E) =>
    D (Real.cos t • p.1+Real.sin t • p.2) (-Real.sin t • p.1+Real.cos t • p.2)
  have hT : 0 < T := by dsimp [T]; positivity
  have hν : ν.real univ = T := by simp [ν,Measure.real,Real.volume_Ioc,hT.le]
  have hdom (t : ℝ) (p : E×E) : (d t p)^2 ≤ 2*C^2*(‖p.1‖^2+‖p.2‖^2) := by
    have hb : ‖-Real.sin t • p.1+Real.cos t • p.2‖ ≤ ‖p.1‖+‖p.2‖ := by
      apply (norm_add_le _ _).trans
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_neg]
      exact add_le_add (by nlinarith [Real.abs_sin_le_one t,norm_nonneg p.1])
        (by nlinarith [Real.abs_cos_le_one t,norm_nonneg p.2])
    have hh : |d t p| ≤ C*(‖p.1‖+‖p.2‖) := by
      change ‖D (Real.cos t • p.1+Real.sin t • p.2) (-Real.sin t • p.1+Real.cos t • p.2)‖ ≤ _
      apply (ContinuousLinearMap.le_opNorm _ _).trans
      exact mul_le_mul (hDC _) hb (norm_nonneg _) hC
    have hh2 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ C*(‖p.1‖+‖p.2‖))).mpr hh
    simp only [sq_abs,mul_pow] at hh2
    have hh3 := mul_nonneg (sq_nonneg C) (sq_nonneg (‖p.1‖-‖p.2‖))
    nlinarith
  have hs : Integrable (fun x : E => ‖x‖^2) γ :=
    (IsGaussian.memLp_id γ 2 (by simp)).norm.integrable_sq
  have hdI : Integrable (fun p : (E×E)×ℝ => (d p.2 p.1)^2) (μ.prod ν) := by
    have hh : Integrable (fun p : (E×E)×ℝ => 2*C^2*(‖p.1.1‖^2+‖p.1.2‖^2)) (μ.prod ν) :=
      (((hs.comp_fst γ).add (hs.comp_snd γ)).const_mul (2*C^2)).comp_fst ν
    apply hh.mono' (by dsimp [d]; fun_prop)
    exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,abs_sq] using hdom p.2 p.1
  have hmF : MemLp F 2 γ := hasFDerivAt_bounded_gaussian_memLp hF hC hDC
  have hdiff : Integrable (fun p : E×E => (F p.2-F p.1)^2) μ := by
    simpa only [Pi.sub_apply] using ((hmF.comp_snd γ).sub (hmF.comp_fst γ)).integrable_sq
  have he : (∫ p : E×E, (F p.2-F p.1)^2 ∂μ) = 2*variance F γ := by
    rw [show (fun p : E×E => (F p.2-F p.1)^2) = fun p => (F p.1-F p.2)^2 by
      funext p; ring]
    exact integral_independent_difference_square γ hmF
  have hn := integral_mono_ae hdiff (hdI.integral_prod_left.const_mul T)
    (ae_of_all _ fun p => gaussian_vector_rotation_path_bound hF hD p.1 p.2)
  rw [he,integral_const_mul,← integral_prod _ hdI,integral_prod_symm _ hdI] at hn
  have hmeans : (∫ t, ∫ p : E×E, (d t p)^2 ∂μ ∂ν) =
      T*(∫ x, ‖D x‖^2 ∂γ) := by
    simp_rw [show ∀ t, (∫ p : E×E, (d t p)^2 ∂μ) = ∫ x, ‖D x‖^2 ∂γ
      from fun t => gaussian_vector_rotation_derivative_square_mean hD hDC t]
    rw [integral_const,hν,smul_eq_mul]
  rw [hmeans] at hn
  dsimp only [T] at hn
  nlinarith

lemma stdGaussian_variance_le_of_fderiv_bound {F : E → ℝ} {D : E → StrongDual ℝ E}
    (hF : ∀ x, HasFDerivAt F (D x) x) (hD : Continuous D)
    {C : ℝ} (hC : 0 ≤ C) (hDC : ∀ x, ‖D x‖ ≤ C) :
    variance F (stdGaussian E) ≤ (Real.pi^2/8)*C^2 := by
  apply (stdGaussian_poincare hF hD hC hDC).trans
  gcongr
  calc
    _ ≤ ∫ _ : E, C^2 ∂stdGaussian E :=
      integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (integrable_const _)
        (ae_of_all _ fun x => (sq_le_sq₀ (norm_nonneg _) hC).mpr (hDC x))
    _ = C^2 := by simp

end SphericalPerceptronFreeEnergy

end

end OAI
