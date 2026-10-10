import OAI.Geometry.LatticeCovering.GaussianMoments

namespace OAI

section
noncomputable section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

lemma gaussian_matrix_char_average {n k : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ]
    (a : ℝ) (t : E k) :
    (∫ g : MatrixSpace n k, charFun μ (a•rowApply g t) ∂stdGaussian (MatrixSpace n k))=
      (radialGaussianAverage μ (a*‖t‖) : ℂ) := by
  have hm : Measurable (fun g : MatrixSpace n k => rowApply g t) :=
    (continuous_rowApply.comp (continuous_id.prodMk continuous_const)).measurable
  have hi := integral_map (μ := stdGaussian (MatrixSpace n k)) hm.aemeasurable
    (f := fun x : E n => charFun μ (a•x)) (by fun_prop)
  rw [←hi,rowApply_gaussian_law,integral_map (by fun_prop) (by fun_prop)]
  simp only [smul_smul]
  exact gaussian_char_average μ _

lemma matrix_phase_char_integrable {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (y : E k) :
    Integrable (fun p : MatrixSpace n k × E k => phase r y p.2*charFun μ ((-r*s)•rowApply p.1 p.2))
      ((stdGaussian (MatrixSpace n k)).prod (stdGaussian (E k))) := by
  apply (integrable_const (1:ℝ)).mono' (by
    have hc := continuous_rowApply (n := n) (k := k)
    unfold phase
    fun_prop)
  exact Filter.Eventually.of_forall (fun p => by
    simpa only [norm_mul,norm_phase,one_mul] using norm_charFun_le_one ((-r*s)•rowApply p.1 p.2))

lemma radialSmoothedModel_eq_average {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (y : E k) : radialSmoothedModel μ s r y=
      Complex.ofReal (∫ g : MatrixSpace n k, smoothedProjection μ s r g y ∂stdGaussian (MatrixSpace n k)) := by
  have H := integral_integral_swap (f := fun g t => phase r y t*charFun μ ((-r*s)•rowApply g t)) (matrix_phase_char_integrable μ s r y)
  simp only [←smoothedProjection_fourier,integral_const_mul,gaussian_matrix_char_average,
    integral_complex_ofReal] at H
  exact H.symm

noncomputable def radialSmoothedDensity {n k : ℕ} (μ : Measure (E n)) (s r : ℝ) (y : E k) : ℝ :=
  (radialSmoothedModel μ s r y).re

lemma radialSmoothedDensity_nonneg {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (y : E k) : 0 ≤ radialSmoothedDensity μ s r y := by
  rw [radialSmoothedDensity,radialSmoothedModel_eq_average,Complex.ofReal_re]
  exact integral_nonneg (fun g => integral_nonneg (fun x => (Real.exp_pos _).le))

lemma radialSmoothedDensity_cast {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (y : E k) : (radialSmoothedDensity μ s r y : ℂ)=radialSmoothedModel μ s r y := by
  simp only [radialSmoothedDensity,radialSmoothedModel_eq_average,Complex.ofReal_re]

lemma radialSmoothedModel_invariant {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (U : E k ≃ₗᵢ[ℝ] E k) (y : E k) :
    radialSmoothedModel μ s r (U y)=radialSmoothedModel μ s r y := by
  have hm : Measurable U := U.continuous.measurable
  have H := integral_map (μ := stdGaussian (E k)) hm.aemeasurable
    (f := fun t : E k => phase r (U y) t*(radialGaussianAverage μ ((-r*s)*‖t‖) : ℂ)) (by
      have hc := continuous_radialGaussianAverage μ
      unfold phase
      fun_prop)
  rw [stdGaussian_map U] at H
  have he (t : E k) : phase r (U y) (U t)=phase r y t := by
    simp only [phase,U.inner_map_map]
  simp only [he,U.norm_map] at H
  exact H

lemma radialSmoothedDensity_norm_eq {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) {y z : E k} (h : ‖y‖=‖z‖) :
    radialSmoothedDensity μ s r y=radialSmoothedDensity μ s r z := by
  have H := radialSmoothedModel_invariant μ s r (Submodule.reflection (ℝ ∙ (y-z))ᗮ) y
  rw [Submodule.reflection_sub h] at H
  exact congrArg Complex.re H.symm

lemma smoothedProjection_real_uniform_error {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (g : MatrixSpace n k) (y : E k) :
    |smoothedProjection μ s r g y-radialSmoothedDensity μ s r y| ≤
      matrixSmoothingError μ (-r*s) g := by
  have H := smoothedProjection_uniform_error μ s r g y
  rw [←radialSmoothedDensity_cast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at H
  exact H

lemma continuous_smoothedProjection {n k : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ]
    (s r : ℝ) : Continuous (fun p : MatrixSpace n k × E k => smoothedProjection μ s r p.1 p.2) := by
  apply continuous_of_dominated (bound := fun _ => (1:ℝ))
  · intro p
    have hc : Continuous (fun x : E n => colApply p.1 x) := continuous_colApply.comp (continuous_const.prodMk continuous_id)
    fun_prop
  · intro p
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using gaussianKernel_bounded r (p.2-s•colApply p.1 x))
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro x
    have hc : Continuous (fun g : MatrixSpace n k => colApply g x) := continuous_colApply.comp (continuous_id.prodMk continuous_const)
    fun_prop

lemma smoothedProjection_le_one {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (g : MatrixSpace n k) (y : E k) : smoothedProjection μ s r g y ≤ 1 := by
  have hi : Integrable (fun x : E n => Real.exp (-r^2*‖y-s•colApply g x‖^2/2)) μ := by
    apply (integrable_const (1:ℝ)).mono' (by
      have hc : Continuous (fun x : E n => colApply g x) := continuous_colApply.comp (continuous_const.prodMk continuous_id)
      fun_prop)
    exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using gaussianKernel_bounded r (y-s•colApply g x))
  calc
    _ ≤ ∫ _ : E n, (1:ℝ) ∂μ := integral_mono hi (integrable_const _) (fun x => (le_abs_self _).trans (gaussianKernel_bounded r _))
    _ = 1 := by simp

section ContinuousProjection
attribute [local irreducible] smoothedProjection

lemma continuous_smoothedProjection_y {n k : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ]
    (s r : ℝ) (g : MatrixSpace n k) : Continuous (smoothedProjection μ s r g) := by
  have hp : Continuous (fun y : E k => (g,y)) := continuous_const.prodMk continuous_id
  exact (continuous_smoothedProjection μ s r).comp hp

lemma continuous_smoothedProjection_g {n k : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ]
    (s r : ℝ) (y : E k) : Continuous (fun g : MatrixSpace n k => smoothedProjection μ s r g y) := by
  have hp : Continuous (fun g : MatrixSpace n k => (g,y)) := continuous_id.prodMk continuous_const
  exact (continuous_smoothedProjection μ s r).comp hp

end ContinuousProjection

lemma norm_smoothedProjection_le {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (g : MatrixSpace n k) (y : E k) : ‖smoothedProjection μ s r g y‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ smoothedProjection μ s r g y from integral_nonneg (fun _ => (Real.exp_pos _).le))]
  exact smoothedProjection_le_one μ s r g y

lemma continuous_radialSmoothedDensity {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) : Continuous (radialSmoothedDensity (k := k) μ s r) := by
  have he : radialSmoothedDensity (k := k) μ s r = fun y =>
      ∫ g : MatrixSpace n k, smoothedProjection μ s r g y ∂stdGaussian (MatrixSpace n k) := by
    ext y
    simp only [radialSmoothedDensity,radialSmoothedModel_eq_average,Complex.ofReal_re]
  rw [he]
  apply continuous_of_dominated (bound := fun _ => (1:ℝ))
  · intro y
    exact (continuous_smoothedProjection_g μ s r y).aestronglyMeasurable
  · intro y
    exact Filter.Eventually.of_forall (fun g => norm_smoothedProjection_le μ s r g y)
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro g
    exact continuous_smoothedProjection_y μ s r g



end SingleLatticeCovering.GaussianProjection
noncomputable section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter GaussianFourier
open scoped ENNReal RealInnerProductSpace ComplexConjugate
abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

def normalizer (k : ℕ) (b : ℝ) : ℝ := (Real.pi/b)^((k:ℝ)/2)
def density {k : ℕ} (b : ℝ) (y : E k) : ℝ := (normalizer k b)⁻¹*Real.exp (-b*‖y‖^2)
def law (k : ℕ) (b : ℝ) : Measure (E k) :=
  volume.withDensity (fun y => ENNReal.ofReal (density b y))

lemma normalizer_pos (k : ℕ) {b : ℝ} (hb : 0 < b) : 0 < normalizer k b := by
  unfold normalizer
  positivity
lemma density_pos {k : ℕ} {b : ℝ} (hb : 0 < b) (y : E k) : 0 < density b y := by
  unfold density
  exact mul_pos (inv_pos.mpr (normalizer_pos k hb)) (Real.exp_pos _)
lemma continuous_density (k : ℕ) (b : ℝ) : Continuous (density (k := k) b) := by
  unfold density
  fun_prop
lemma integrable_kernel {k : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : E k => Real.exp (-b*‖y‖^2)) volume := by
  have H := integrable_cexp_neg_mul_sq_norm_add (V := E k) (b := (b:ℂ)) hb 0 (0:E k)
  have H' := H.re
  simpa only [zero_mul,add_zero,←Complex.ofReal_pow,←Complex.ofReal_mul,←Complex.ofReal_neg,
    RCLike.re_to_complex, Complex.exp_ofReal_re] using H'
lemma integral_kernel {k : ℕ} {b : ℝ} (hb : 0 < b) :
    (∫ y : E k, Real.exp (-b*‖y‖^2))=normalizer k b := by
  simpa only [normalizer,finrank_euclideanSpace_fin] using integral_rexp_neg_mul_sq_norm (V := E k) hb
lemma integrable_density {k : ℕ} {b : ℝ} (hb : 0 < b) : Integrable (density (k := k) b) volume :=
  (integrable_kernel hb).const_mul _
lemma integral_density {k : ℕ} {b : ℝ} (hb : 0 < b) : (∫ y : E k, density b y)=1 := by
  unfold density
  rw [integral_const_mul,integral_kernel hb,inv_mul_cancel₀ (ne_of_gt (normalizer_pos k hb))]
lemma law_probability (k : ℕ) {b : ℝ} (hb : 0 < b) : IsProbabilityMeasure (law k b) := by
  constructor
  rw [law,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [←ofReal_integral_eq_lintegral_ofReal (integrable_density hb)
    (Filter.Eventually.of_forall (fun y => (density_pos hb y).le)),integral_density hb]
  norm_num

lemma integral_law {k : ℕ} {b : ℝ} (hb : 0 < b) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E k → F) :
    (∫ y, f y ∂law k b) = ∫ y, density b y • f y := by
  have H := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure (E k)))
    (f := fun y => ENNReal.ofReal (density b y)) (g := f)
    ((ENNReal.continuous_ofReal.comp (continuous_density k b)).measurable)
    (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top))
  simpa only [law,ENNReal.toReal_ofReal (density_pos hb _).le] using H

lemma charFun_law {k : ℕ} {b : ℝ} (hb : 0 < b) (t : E k) :
    charFun (law k b) t=Complex.exp (-(‖t‖:ℂ)^2/(4*b)) := by
  rw [charFun_apply,integral_law hb]
  have he (y : E k) : density b y • Complex.exp (⟪y,t⟫*Complex.I)=
      ((normalizer k b)⁻¹:ℂ)*Complex.exp (-(b:ℂ)*‖y‖^2+Complex.I*⟪t,y⟫) := by
    rw [density,Complex.real_smul]
    push_cast
    rw [mul_assoc,←Complex.exp_add,real_inner_comm y t]
    congr 2
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_cexp_neg_mul_sq_norm_add (V := E k) (b := (b:ℂ)) hb Complex.I t]
  have hc : (Real.pi/(b:ℂ))^((Module.finrank ℝ (E k):ℂ)/2)=(normalizer k b:ℂ) := by
    rw [normalizer,finrank_euclideanSpace_fin,←Complex.ofReal_div,Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  have hn : (normalizer k b:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (normalizer_pos k hb)
  rw [hc,←mul_assoc,inv_mul_cancel₀ hn,one_mul]
  congr 1
  rw [Complex.I_sq]
  ring

lemma stdGaussian_eq_law (k : ℕ) : stdGaussian (E k)=law k (1/2) := by
  let := law_probability k (show (0:ℝ) < 1/2 by norm_num)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian,charFun_law (by norm_num)]
  congr 1
  push_cast
  ring


end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter GaussianFourier
open scoped ENNReal RealInnerProductSpace

lemma density_mul_exp {k : ℕ} (b t : ℝ) (y : E k) :
    density b y*Real.exp (t*‖y‖^2)=(normalizer k b)⁻¹*Real.exp (-(b-t)*‖y‖^2) := by
  unfold density
  rw [mul_assoc,←Real.exp_add]
  congr 2
  ring

lemma integrable_exp_norm_sq {k : ℕ} {b t : ℝ} (hb : 0 < b) (ht : t < b) :
    Integrable (fun y : E k => Real.exp (t*‖y‖^2)) (law k b) := by
  have H := integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure (E k)))
    (f := fun y => ENNReal.ofReal (density b y)) (g := fun y => Real.exp (t*‖y‖^2))
    ((ENNReal.continuous_ofReal.comp (continuous_density k b)).measurable)
    (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top))
  apply H.mpr
  simp only [ENNReal.toReal_ofReal (density_pos hb _).le,smul_eq_mul,density_mul_exp]
  exact (integrable_kernel (sub_pos.mpr ht)).const_mul _

lemma integral_exp_norm_sq {k : ℕ} {b t : ℝ} (hb : 0 < b) (ht : t < b) :
    (∫ y : E k, Real.exp (t*‖y‖^2) ∂law k b)=(normalizer k b)⁻¹*normalizer k (b-t) := by
  rw [integral_law hb]
  simp only [smul_eq_mul,density_mul_exp]
  rw [integral_const_mul,integral_kernel (sub_pos.mpr ht)]

lemma normalizer_eq_exp (k : ℕ) {b : ℝ} (hb : 0 < b) :
    normalizer k b=Real.exp (((k:ℝ)/2)*(Real.log Real.pi-Real.log b)) := by
  unfold normalizer
  rw [Real.rpow_def_of_pos (div_pos Real.pi_pos hb),Real.log_div Real.pi_ne_zero (ne_of_gt hb)]
  congr 1
  ring

lemma stdGaussian_laplace_norm_sq {k : ℕ} {a : ℝ} (ha : a < 1) :
    (∫ y : E k, Real.exp (a*‖y‖^2/2) ∂stdGaussian (E k))=
      Real.exp (-((k:ℝ)/2)*Real.log (1-a)) := by
  rw [stdGaussian_eq_law]
  have he (y : E k) : a*‖y‖^2/2=(a/2)*‖y‖^2 := by ring
  simp_rw [he]
  rw [integral_exp_norm_sq (by norm_num) (by linarith),
    normalizer_eq_exp k (by norm_num),normalizer_eq_exp k (by linarith),
    ←Real.exp_neg,←Real.exp_add]
  have hl : Real.log ((1:ℝ)/2-a/2)=Real.log ((1:ℝ)/2)+Real.log (1-a) := by
    rw [show (1:ℝ)/2-a/2=(1/2)*(1-a) by ring,Real.log_mul (by norm_num) (by linarith)]
  rw [hl]
  congr 1
  ring

lemma stdGaussian_integrable_exp_norm_sq {k : ℕ} {a : ℝ} (ha : a < 1) :
    Integrable (fun y : E k => Real.exp (a*‖y‖^2/2)) (stdGaussian (E k)) := by
  rw [stdGaussian_eq_law]
  have he (y : E k) : a*‖y‖^2/2=(a/2)*‖y‖^2 := by ring
  simp_rw [he]
  exact integrable_exp_norm_sq (by norm_num) (by linarith)


end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter GaussianFourier
open scoped ENNReal RealInnerProductSpace Topology

lemma integral_real_quadratic {k : ℕ} {b : ℝ} (hb : 0 < b) (c : ℝ) (w : E k) :
    (∫ y : E k, Real.exp (-b*‖y‖^2+c*⟪w,y⟫))=
      normalizer k b*Real.exp (c^2*‖w‖^2/(4*b)) := by
  have H := integral_cexp_neg_mul_sq_norm_add (V := E k) (b := (b:ℂ)) hb (c:ℂ) w
  have hc : (Real.pi/(b:ℂ))^((Module.finrank ℝ (E k):ℂ)/2)=(normalizer k b:ℂ) := by
    rw [normalizer,finrank_euclideanSpace_fin,←Complex.ofReal_div,Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  rw [hc] at H
  apply Complex.ofReal_injective
  rw [←integral_complex_ofReal]
  convert H using 1 <;> push_cast <;> rfl

lemma normalizer_ratio_half (k : ℕ) {v : ℝ} (hv : 0 < v) :
    (normalizer k (1/2))⁻¹*normalizer k (v/2)=Real.exp (-((k:ℝ)/2)*Real.log v) := by
  rw [normalizer_eq_exp k (by norm_num),normalizer_eq_exp k (by positivity),←Real.exp_neg,←Real.exp_add]
  have hh : Real.log (v/2)= Real.log ((1:ℝ)/2)+Real.log v := by
    rw [show v/2=(1/2)*v by ring,Real.log_mul (by norm_num) (ne_of_gt hv)]
  rw [hh]
  congr 1
  ring

lemma gaussian_convolution_kernel {k : ℕ} (a r : ℝ) (y : E k) :
    (∫ z : E k, Real.exp (-r^2*‖y-a•z‖^2/2) ∂stdGaussian (E k))=
      Real.exp (-((k:ℝ)/2)*Real.log (1+r^2*a^2)-r^2*‖y‖^2/(2*(1+r^2*a^2))) := by
  have hv : 0 < 1+r^2*a^2 := by positivity
  rw [stdGaussian_eq_law,integral_law (by norm_num)]
  have he (z : E k) : density (1/2) z • Real.exp (-r^2*‖y-a•z‖^2/2)=
      ((normalizer k (1/2))⁻¹*Real.exp (-r^2*‖y‖^2/2))*
        Real.exp (-((1+r^2*a^2)/2)*‖z‖^2+(r^2*a)*⟪y,z⟫) := by
    rw [density,smul_eq_mul,mul_assoc,←Real.exp_add,mul_assoc,←Real.exp_add]
    congr 2
    rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_right]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_real_quadratic (show 0 < (1+r^2*a^2)/2 by positivity)]
  have hre : ((normalizer k (1/2))⁻¹*Real.exp (-r^2*‖y‖^2/2))*
      (normalizer k ((1+r^2*a^2)/2)*Real.exp ((r^2*a)^2*‖y‖^2/(4*((1+r^2*a^2)/2))))=
      ((normalizer k (1/2))⁻¹*normalizer k ((1+r^2*a^2)/2))*
        (Real.exp (-r^2*‖y‖^2/2)*Real.exp ((r^2*a)^2*‖y‖^2/(4*((1+r^2*a^2)/2)))) := by ring
  rw [hre,normalizer_ratio_half k hv,←Real.exp_add,←Real.exp_add]
  congr 1
  field_simp
  ring


end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter GaussianDensity
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace Topology

lemma colApply_gaussian_law {n k : ℕ} (x : Isotropization.E n) :
    (stdGaussian (MatrixSpace n k)).map (fun g => colApply g x)=
      (stdGaussian (Isotropization.E k)).map (fun y => ‖x‖•y) := by
  have hm : Measurable (fun g : MatrixSpace n k => colApply g x) :=
    (continuous_colApply.comp (continuous_id.prodMk continuous_const)).measurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply,integral_map hm.aemeasurable (by fun_prop),
    charFun_apply,integral_map (by fun_prop) (by fun_prop)]
  have he (g : MatrixSpace n k) : ⟪colApply g x,t⟫=⟪g,tensor x t⟫ := by
    rw [inner_colApply]
    exact (real_inner_comm _ _).trans (inner_rowApply g x t)
  have he' (y : Isotropization.E k) : (‖x‖*⟪y,t⟫ : ℝ)=⟪y,‖x‖•t⟫ := by rw [inner_smul_right]
  simp only [he,inner_smul_left,conj_trivial,he',←charFun_apply,charFun_stdGaussian]
  congr 1
  rw [←Complex.ofReal_pow,←Complex.ofReal_pow,norm_tensor_sq,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),mul_pow]

lemma kernel_normalization {k : ℕ} {r : ℝ} (hr : r ≠ 0) (a : ℝ) (y : Isotropization.E k) :
    (normalizer k (r^2/2))⁻¹*
      Real.exp (-((k:ℝ)/2)*Real.log (1+r^2*a^2)-r^2*‖y‖^2/(2*(1+r^2*a^2)))=
      density (1/(2*(a^2+1/r^2))) y := by
  have hr2 : 0 < r^2 := sq_pos_of_ne_zero hr
  have hv : 0 < a^2+1/r^2 := by positivity
  have hv' : 0 < 1+r^2*a^2 := by positivity
  have hb : 0 < 1/(2*(a^2+1/r^2)) := by positivity
  have hlog : Real.log (1/(2*(a^2+1/r^2)))=
      Real.log (r^2/2)-Real.log (1+r^2*a^2) := by
    rw [←Real.log_div (by positivity) (ne_of_gt hv')]
    congr 1
    field_simp
    ring
  rw [density,normalizer_eq_exp k (by positivity),normalizer_eq_exp k hb,
    ←Real.exp_neg,←Real.exp_neg,←Real.exp_add,←Real.exp_add,hlog]
  congr 1
  field_simp
  ring

lemma radialSmoothedDensity_mixture {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (s r : ℝ) (y : Isotropization.E k) :
    radialSmoothedDensity μ s r y=
      ∫ x, Real.exp (-((k:ℝ)/2)*Real.log (1+r^2*(s*‖x‖)^2)-
        r^2*‖y‖^2/(2*(1+r^2*(s*‖x‖)^2))) ∂μ := by
  have hj : Integrable (fun p : MatrixSpace n k × Isotropization.E n =>
      Real.exp (-r^2*‖y-s•colApply p.1 p.2‖^2/2)) ((stdGaussian (MatrixSpace n k)).prod μ) := by
    apply (integrable_const (1:ℝ)).mono' (by
      have hc := continuous_colApply (n := n) (k := k)
      fun_prop)
    exact Filter.Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs] using gaussianKernel_bounded r (y-s•colApply p.1 p.2))
  rw [radialSmoothedDensity,radialSmoothedModel_eq_average,Complex.ofReal_re]
  unfold smoothedProjection
  rw [integral_integral_swap hj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hm : Measurable (fun g : MatrixSpace n k => colApply g x) :=
    (continuous_colApply.comp (continuous_id.prodMk continuous_const)).measurable
  dsimp only
  rw [←integral_map (μ := stdGaussian (MatrixSpace n k)) hm.aemeasurable (f := fun z => Real.exp (-r^2*‖y-s•z‖^2/2)) (by fun_prop),
    colApply_gaussian_law,integral_map (by fun_prop) (by fun_prop)]
  simp only [smul_smul]
  exact gaussian_convolution_kernel _ _ _

lemma normalized_radialSmoothedDensity_mixture {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (s : ℝ) {r : ℝ} (hr : r ≠ 0) (y : Isotropization.E k) :
    (normalizer k (r^2/2))⁻¹*radialSmoothedDensity μ s r y=
      ∫ x, density (1/(2*((s*‖x‖)^2+1/r^2))) y ∂μ := by
  rw [radialSmoothedDensity_mixture,←integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => kernel_normalization hr _ _)


end SingleLatticeCovering.GaussianProjection





open MeasureTheory Filter Set
open scoped Topology
noncomputable section



namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open SingleLatticeCovering.SharpYoung
open scoped ENNReal

lemma weighted_transport_inequality {u v a b : ℝ}
    (hu : 0 < u) (hv : 0 < v) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    u ≤ (a+b*(u/v))*(u^a*v^b) := by
  have hgm : (u/v)^b ≤ a+b*(u/v) := by
    simpa only [Real.one_rpow,one_mul,mul_one] using
      Real.geom_mean_le_arith_mean2_weighted ha hb (show (0:ℝ) ≤ 1 by norm_num)
        (div_pos hu hv).le hab
  have he : (u/v)^b*(u^a*v^b)=u := by
    rw [Real.div_rpow hu.le hv.le]
    have hpow : v^b ≠ 0 := (Real.rpow_pos_of_pos hv _).ne'
    calc
      u^b/v^b*(u^a*v^b) = u^a*u^b := by field_simp
      _ = u^(a+b) := (Real.rpow_add hu _ _).symm
      _ = u := by rw [hab,Real.rpow_one]
  calc
    u = (u/v)^b*(u^a*v^b) := he.symm
    _ ≤ (a+b*(u/v))*(u^a*v^b) := mul_le_mul_of_nonneg_right hgm (by positivity)




theorem positive_probability_lintegral (f g : PositiveDensity) {h : ℝ → ℝ}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hh : ∀ x y, f x ^ a * g y ^ b ≤ h (a*x+b*y)) :
    1 ≤ ∫⁻ z, ENNReal.ofReal (h z) := by
  let T : ℝ → ℝ := densityTransport f g
  let W : ℝ → ℝ := fun x => a*x+b*T x
  let W' : ℝ → ℝ := fun x => a+b*(f x/g (T x))
  have hT : StrictMono T := (densityTransport f g).strictMono
  have hW : StrictMono W := by
    intro x y hxy
    exact add_lt_add (mul_lt_mul_of_pos_left hxy ha)
      (mul_lt_mul_of_pos_left (hT hxy) hb)
  have hd (x : ℝ) : HasDerivAt W (W' x) x := by
    simpa only [W,W',T,id_eq,Pi.add_def,mul_one] using
      ((hasDerivAt_id x).const_mul a).add ((densityTransport_hasDerivAt f g x).const_mul b)
  have hp (x : ℝ) : 0 < W' x := by
    dsimp [W']; exact add_pos ha (mul_pos hb (div_pos (f.positive x) (g.positive _)))
  have hi : (∫⁻ x, ENNReal.ofReal (f x))=1 := by
    rw [←ofReal_integral_eq_lintegral_ofReal f.integrable
      (Filter.Eventually.of_forall fun x => (f.positive x).le),f.integral_one]
    norm_num
  calc
    1 = ∫⁻ x, ENNReal.ofReal (f x) := hi.symm
    _ ≤ ∫⁻ x, ENNReal.ofReal |W' x| *ENNReal.ofReal (h (W x)) := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (f x) ≤ ENNReal.ofReal |W' x| * ENNReal.ofReal (h (W x))
      rw [abs_of_pos (hp x),←ENNReal.ofReal_mul (hp x).le]
      apply ENNReal.ofReal_le_ofReal
      exact (weighted_transport_inequality (f.positive x) (g.positive (T x)) ha.le hb.le hab).trans
        (mul_le_mul_of_nonneg_left (hh x (T x)) (hp x).le)
    _ = ∫⁻ z in W '' univ, ENNReal.ofReal (h z) := by
      symm
      simpa using lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
        (fun x _ => (hd x).hasDerivWithinAt) hW.injective.injOn (fun z => ENNReal.ofReal (h z))
    _ ≤ ∫⁻ z, ENNReal.ofReal (h z) :=
      lintegral_mono' Measure.restrict_le_self (le_refl _)


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open SingleLatticeCovering.SharpYoung SingleLatticeCovering.SimplexYoung
open scoped ENNReal



theorem positive_integral {f g h : ℝ → ℝ}
    (fc : Continuous f) (gc : Continuous g) (fp : ∀ x, 0 < f x) (gp : ∀ x, 0 < g x)
    (fi : Integrable f volume) (gi : Integrable g volume) (hi : Integrable h volume)
    (hn : ∀ x, 0 ≤ h x) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hfg : ∀ x y, f x^a*g y^b ≤ h (a*x+b*y)) :
    (∫ x, f x)^a*(∫ y, g y)^b ≤ ∫ z, h z := by
  let F := normalizePositiveDensity f fc fp fi
  let G := normalizePositiveDensity g gc gp gi
  let M := (∫ x, f x)^a*(∫ y, g y)^b
  have hfpos := integral_pos_of_continuous_density fp fi
  have hgpos := integral_pos_of_continuous_density gp gi
  have hM : 0 < M := mul_pos (Real.rpow_pos_of_pos hfpos _) (Real.rpow_pos_of_pos hgpos _)
  have hh : ∀ x y, F x^a*G y^b ≤ (h (a*x+b*y))/M := by
    intro x y
    dsimp [F,G,normalizePositiveDensity,M]
    rw [Real.div_rpow (fp x).le hfpos.le,Real.div_rpow (gp y).le hgpos.le,
      div_mul_div_comm]
    exact div_le_div_of_nonneg_right (hfg x y) hM.le
  have hineq := positive_probability_lintegral F G (h := fun z => h z/M) ha hb hab hh
  rw [←ofReal_integral_eq_lintegral_ofReal (hi.div_const M)
    (Filter.Eventually.of_forall (fun z => div_nonneg (hn z) hM.le)),integral_div] at hineq
  have ht : (1:ℝ) ≤ (∫ z, h z)/M := by
    exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg (integral_nonneg hn) hM.le)).mp (by simpa using hineq)
  have := (le_div_iff₀ hM).mp ht
  simpa only [one_mul] using this


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

abbrev RV (d : ℕ) := Fin d → ℝ

def gaussianKernel (d : ℕ) (c : ℝ) (x : RV d) : ℝ :=
  Real.exp (-c*∑ i, (x i)^2)

lemma gaussianKernel_prod (d : ℕ) (c : ℝ) (x : RV d) :
    gaussianKernel d c x = ∏ i, Real.exp (-c*(x i)^2) := by
  rw [gaussianKernel,Finset.mul_sum,Real.exp_sum]

lemma gaussianKernel_pos (d : ℕ) (c : ℝ) (x : RV d) : 0 < gaussianKernel d c x := Real.exp_pos _

lemma gaussianKernel_le_one (d : ℕ) {c : ℝ} (hc : 0 ≤ c) (x : RV d) :
    gaussianKernel d c x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma continuous_gaussianKernel (d : ℕ) (c : ℝ) : Continuous (gaussianKernel d c) := by
  unfold gaussianKernel
  fun_prop

lemma integrable_gaussianKernel (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (gaussianKernel d c) volume := by
  have H : Integrable (fun x : RV d => ∏ i, Real.exp (-c*(x i)^2)) volume :=
    Integrable.fintype_prod (fun _ : Fin d => integrable_exp_neg_mul_sq hc)
  have he : gaussianKernel d c = (fun x : RV d => ∏ i, Real.exp (-c*(x i)^2)) :=
    funext (gaussianKernel_prod d c)
  rw [he]
  exact H

lemma integral_gaussianKernel (d : ℕ) (c : ℝ) :
    (∫ x, gaussianKernel d c x) = (Real.sqrt (Real.pi/c))^d := by
  simp_rw [gaussianKernel_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun _ : Fin d => fun t : ℝ => Real.exp (-c*t^2))]
  simp only [integral_gaussian,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma gaussianKernel_cons (d : ℕ) (c t : ℝ) (y : RV d) :
    gaussianKernel (d+1) c (Fin.cons t y)=Real.exp (-c*t^2)*gaussianKernel d c y := by
  simp only [gaussianKernel,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_add,Real.exp_add]



def GaussianBound {d : ℕ} (f : RV d → ℝ) : Prop :=
  ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ x, |f x| ≤ A*gaussianKernel d c x

lemma GaussianBound.integrable {d : ℕ} {f : RV d → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) : Integrable f volume := by
  obtain ⟨A,c,hA,hc',hb⟩ := hf
  apply ((integrable_gaussianKernel d hc').const_mul A).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)

lemma gaussian_slice_dominant {d : ℕ} {f : RV (d+1) → ℝ} {A c : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hbound : ∀ x, |f x| ≤ A*gaussianKernel (d+1) c x)
    (y : RV d) (t : ℝ) : |f (Fin.cons t y)| ≤ A*Real.exp (-c*t^2) := by
  calc
    _ ≤ A*gaussianKernel (d+1) c (Fin.cons t y) := hbound _
    _ = (A*Real.exp (-c*t^2))*gaussianKernel d c y := by rw [gaussianKernel_cons,mul_assoc]
    _ ≤ A*Real.exp (-c*t^2) := mul_le_of_le_one_right (by positivity) (gaussianKernel_le_one d hc y)

lemma GaussianBound.integrable_slice {d : ℕ} {f : RV (d+1) → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) (y : RV d) :
    Integrable (fun t : ℝ => f (Fin.cons t y)) volume := by
  obtain ⟨A,c,hA,hc',hb⟩ := hf
  apply ((integrable_exp_neg_mul_sq hc').const_mul A).mono'
    (hc.comp (continuous_id.finCons continuous_const)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs,Function.comp_def,id_eq] using gaussian_slice_dominant hA.le hc'.le hb y t)

def marginalOne {d : ℕ} (f : RV (d+1) → ℝ) (y : RV d) : ℝ :=
  ∫ t, f (Fin.cons t y)

lemma GaussianBound.continuous_marginalOne {d : ℕ} {f : RV (d+1) → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) : Continuous (marginalOne f) := by
  obtain ⟨A,c,hA,hc',hb⟩ := hf
  apply continuous_of_dominated
      (bound := fun t : ℝ => A*Real.exp (-c*t^2))
  · intro y
    exact (hc.comp (continuous_id.finCons continuous_const)).aestronglyMeasurable
  · intro y
    exact Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs,Function.comp_def,id_eq] using gaussian_slice_dominant hA.le hc'.le hb y t)
  · exact (integrable_exp_neg_mul_sq hc').const_mul A
  · exact Filter.Eventually.of_forall (fun t => hc.comp (continuous_const.finCons continuous_id))

lemma marginalOne_positive {d : ℕ} {f : RV (d+1) → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) (hp : ∀ x, 0 < f x) (y : RV d) :
    0 < marginalOne f y :=
  SingleLatticeCovering.SimplexYoung.integral_pos_of_continuous_density
    (fun t => hp (Fin.cons t y)) (hf.integrable_slice hc y)

lemma GaussianBound.for_marginalOne {d : ℕ} {f : RV (d+1) → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) : GaussianBound (marginalOne f) := by
  obtain ⟨A,c,hA,hc',hb⟩ := hf
  have hg : GaussianBound f := ⟨A,c,hA,hc',hb⟩
  refine ⟨A*Real.sqrt (Real.pi/c),c,mul_pos hA (Real.sqrt_pos.mpr (div_pos Real.pi_pos hc')),hc',?_⟩
  intro y
  have hi := hg.integrable_slice hc y
  calc
    |marginalOne f y| ≤ ∫ t, |f (Fin.cons t y)| := by
      simpa only [Real.norm_eq_abs,marginalOne] using norm_integral_le_integral_norm (fun t => f (Fin.cons t y))
    _ ≤ ∫ t, (A*gaussianKernel d c y)*Real.exp (-c*t^2) := by
      apply integral_mono hi.norm ((integrable_exp_neg_mul_sq hc').const_mul _)
      intro t
      calc
        _ ≤ A*gaussianKernel (d+1) c (Fin.cons t y) := hb _
        _ = _ := by rw [gaussianKernel_cons]; ring
    _ = (A*Real.sqrt (Real.pi/c))*gaussianKernel d c y := by
      rw [integral_const_mul,integral_gaussian]
      ring

lemma integral_marginalOne {d : ℕ} {f : RV (d+1) → ℝ} (hi : Integrable f volume) :
    (∫ y, marginalOne f y) = ∫ x, f x := by
  have hm := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm
  have he := hm.integral_comp' f
  have hj := (hm.integrable_comp hi.aestronglyMeasurable).mpr hi
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv_zero,Function.comp_def] at he hj
  rw [←he]
  exact (integral_prod_symm (fun p : ℝ × RV d => f (Fin.cons p.1 p.2)) hj).symm


end SingleLatticeCovering.Prekopa


end
end
end
end

end OAI
