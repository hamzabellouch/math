import Mathlib
import OAI.Probability.LogConcave.Sampling.TranslationIntegrationByParts

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma conditionalPotential_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r ρ : ℝ) (y : Point d) :
    ContDiff ℝ 2 (conditionalPotential F x r ρ y) :=
  (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _).add
    (hF.smooth.comp (contDiff_const.add (contDiff_id.const_smul r)))

lemma conditionalPotential_gradient {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r ρ : ℝ) (y z : Point d) :
    gradient (conditionalPotential F x r ρ y) z=
      (1/(1-ρ^2)) • (z-ρ • y)+r • primitiveField F x r z := by
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hg := (hasStrictFDerivAt_norm_sq (z-ρ • y)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const (ρ • y))
  have hh := (hF.smooth.differentiable (by norm_num) (x+r • z)).hasFDerivAt.comp z
    (((hasFDerivAt_id z).const_smul r).const_add x)
  have hd := (hg.const_smul (1/(2*(1-ρ^2)))).add hh
  convert! hd using 1
  · funext w
    simp only [conditionalPotential,Pi.add_apply,Pi.smul_apply,Function.comp_apply,smul_eq_mul,id_eq]
    ring
  ext v
  simp only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul,InnerProductSpace.toDual_apply_apply,
    inner_add_left,real_inner_smul_left,innerSL_apply_apply,map_smul,←toDual_gradient,
    primitiveField]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma conditionalPotential_gradient_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r) (ha : 0<1-ρ^2)
    (y : Point d) : LipschitzWith ⟨1/(1-ρ^2)+(lam:ℝ)*r^2,by positivity⟩
      (gradient (conditionalPotential F x r ρ y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [conditionalPotential_gradient hF,dist_eq_norm]
  have he : (1/(1-ρ^2)) • (u-ρ • y)+r • primitiveField F x r u-
      ((1/(1-ρ^2)) • (v-ρ • y)+r • primitiveField F x r v)=
      (1/(1-ρ^2)) • (u-v)+r • (primitiveField F x r u-primitiveField F x r v) := by
    simp only [smul_sub]; abel
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hr,
    abs_of_pos (div_pos zero_lt_one ha)]
  have hh := (primitiveField_lipschitz hF x hr).dist_le_mul u v
  simp only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_mk] at hh
  have hb := mul_le_mul_of_nonneg_left hh hr
  change _ ≤ (1/(1-ρ^2)+(lam:ℝ)*r^2)*‖u-v‖
  nlinarith

lemma conditional_identity_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    Integrable (fun z => z) (gibbs (conditionalPotential F x r ρ y)) := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  exact (Appell.HasGrowth.lipschitz (LipschitzWith.id (α:=Point d))).integrable
    continuous_id.aestronglyMeasurable
    (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments

lemma integral_scaled_affine_add {d : ℕ} {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    {h : Point d → Point d} (hi : Integrable (fun z => z) μ) (hh : Integrable h μ)
    (c r : ℝ) (y : Point d) :
    (∫ z,c • (z-y)+r • h z ∂μ)=c • ((∫ z,z ∂μ)-y)+r • ∫ z,h z ∂μ := by
  have hi₁ : Integrable (fun z => c • (z-y)) μ := (hi.sub (integrable_const y)).smul c
  have hi₂ : Integrable (fun z => r • h z) μ := hh.smul r
  rw [integral_add hi₁ hi₂,integral_smul,integral_smul,
    integral_sub hi (integrable_const y),integral_const,probReal_univ,one_smul]

theorem conditional_mean_identity {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    (∫ z,z ∂gibbs (conditionalPotential F x r ρ y))=
      ρ • y-((1-ρ^2)*r) • conditionalFieldMean F x r ρ y := by
  have ha := (probability_time hρ0 hρ1).1
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hz := integral_gradient_gibbs_zero
    ((conditionalPotential_smooth hF x r ρ y).of_le (by norm_num))
    (conditional_hasGaussianLowerTail hF x hr hl hρ0 hρ1 y)
    (conditionalPotential_gradient_lipschitz hF x hr ha y)
  have hi := conditional_identity_integrable hF x hr hl hρ0 hρ1 y
  have hf := conditionalField_integrable hF x hr hl hρ0 hρ1 y
  simp_rw [conditionalPotential_gradient hF] at hz
  have he := integral_scaled_affine_add (μ:=μ) hi hf (1/(1-ρ^2)) r (ρ • y)
  rw [he] at hz
  change (1/(1-ρ^2)) • ((∫ z,z ∂μ)-ρ • y)+r • conditionalFieldMean F x r ρ y=0 at hz
  have hh := congrArg (fun z : Point d => (1-ρ^2) • z) hz
  rw [smul_add,smul_smul,smul_smul,smul_zero,mul_one_div_cancel ha.ne',one_smul] at hh
  apply eq_sub_iff_add_eq.mpr
  have hh' : (∫ z,z ∂μ)+((1-ρ^2)*r) • conditionalFieldMean F x r ρ y-ρ • y=0 := by
    convert! hh using 1; abel
  exact sub_eq_zero.mp hh'
end LogConcaveSampling
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma hasGradientAt_log_tiltedIntegral {d : ℕ} {H : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) (θ : Point d) :
    HasGradientAt (fun θ => Real.log (tiltedIntegral H (fun _ => (1:ℝ)) θ))
      (tiltedExpectation H (fun z => z) θ) θ := by
  have hd := (hasFDerivAt_tiltedIntegral H hH continuous_const ht (growth_const (1:ℝ)) θ).log
    (tilted_partition_pos hH ht θ).ne'
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hd using 1
  ext v
  have hi := integrable_tilted H hH continuous_id ht (growth_of_lipschitz (LipschitzWith.id (α:=Point d))) θ
  have hiD := integrable_tilted H hH (continuous_tiltDerivativeIntegrand continuous_const) ht
    (growth_tiltDerivativeIntegrand (growth_const (1:ℝ))) θ
  simp only [tiltedExpectation,InnerProductSpace.toDual_apply_apply,real_inner_smul_left,
    smul_apply,smul_eq_mul]
  congr 1
  rw [real_inner_comm]
  simp only [tiltedIntegral]
  simp only [id_eq] at hi
  rw [←integral_inner (𝕜:=ℝ) hi v]
  change (∫ z,inner ℝ v (Real.exp (inner ℝ θ z-H z) • z))=
    (∫ z,Real.exp (inner ℝ θ z-H z) • tiltDerivativeIntegrand (fun _ => (1:ℝ)) z) v
  rw [ContinuousLinearMap.integral_apply hiD]
  apply integral_congr_ae
  filter_upwards [] with z
  simp [tiltDerivativeIntegrand,real_inner_comm,mul_comm,real_inner_smul_right]

lemma quadraticTilt_eq_tilted {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : Point d → ℝ) (h : Point d → E) (θ : Point d) (c : ℝ) :
    quadraticTilt H h (θ,c)=tiltedIntegral (fun z => H z+c*‖z‖^2) h θ := by
  unfold quadraticTilt tiltedIntegral
  congr 1; funext z; congr 2; dsimp; ring

def interpolationPotential {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y : Point d) : ℝ := ‖y‖^2/(2*(1-ρ^2))-
      Real.log (quadraticTilt (primitivePotential F x r) (fun _ => (1:ℝ))
        (conditionalParameter (ρ,y)))

lemma hasGradientAt_interpolationPotential {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    HasGradientAt (interpolationPotential F x r ρ)
      (y+(r*ρ) • conditionalFieldMean F x r ρ y) y := by
  have ha := (probability_time hρ0 hρ1).1
  let a := 1-ρ^2
  let H := fun z => primitivePotential F x r z+(ρ^2/(2*a))*‖z‖^2
  have hc : Continuous H := (hF.continuous_potential x r).add
    (continuous_const.mul (continuous_norm.pow 2))
  have ht : HasGaussianLowerTail H := by
    obtain ⟨m,hm,C,hC⟩ := hF.hasGaussianLowerTail x hr (by linarith)
    refine ⟨m,hm,C,fun z => ?_⟩
    have hp : 0≤(ρ^2/(2*a))*‖z‖^2 := by dsimp [a]; positivity
    dsimp [H]; linarith [hC z]
  have hd := (hasGradientAt_log_tiltedIntegral hc ht ((ρ/a) • y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_smul (ρ/a))
  have hn := ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_smul (1/(2*a))).sub hd
  have he : tiltedExpectation H (fun z => z) ((ρ/a) • y)=
      ρ • y-(a*r) • conditionalFieldMean F x r ρ y := by
    rw [←conditional_mean_identity hF x hr hl hρ0 hρ1 y]
    rw [conditional_integral_quadratic hF x hr (by linarith)
      (by linarith) y]
    simp only [quadraticExpectation,conditionalParameter,quadraticTilt_eq_tilted,a,tiltedExpectation,H]
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hn using 1
  · funext z
    simp only [interpolationPotential,conditionalParameter,quadraticTilt_eq_tilted,
      Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Function.comp_apply,H,a]
    ring
  ext v
  simp only [sub_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul,InnerProductSpace.toDual_apply_apply,
    real_inner_smul_left,inner_add_left,inner_smul_right,he,inner_sub_left,
    innerSL_apply_apply]
  dsimp [a]
  field_simp
  ring

lemma interpolationPotential_gradient {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    gradient (interpolationPotential F x r ρ) y=
      y+(r*ρ) • conditionalFieldMean F x r ρ y :=
  (hasGradientAt_interpolationPotential hF x hr hl hρ0 hρ1 y).gradient
end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

lemma map_snd_withDensity {E G : Type*} [MeasurableSpace E] [MeasurableSpace G]
    (μ : Measure E) (ν : Measure G) [SFinite μ] [SFinite ν]
    {w : E × G → ℝ≥0∞} (hw : Measurable w) :
    ((μ.prod ν).withDensity w).map Prod.snd=
      ν.withDensity (fun y => ∫⁻ x,w (x,y) ∂μ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_snd]
  change (∫⁻ a, (f ∘ Prod.snd) a ∂(μ.prod ν).withDensity w)=_
  rw [lintegral_withDensity_eq_lintegral_mul _ hw (hf.comp measurable_snd),
    lintegral_withDensity_eq_lintegral_mul _ hw.lintegral_prod_left' hf,
    lintegral_prod_symm _ (hw.mul (hf.comp measurable_snd)).aemeasurable]
  apply lintegral_congr
  intro y
  exact lintegral_mul_const (f y) (hw.comp (measurable_id.prodMk measurable_const))

lemma probability_density_eq_gibbs {d : ℕ} {H : Point d → ℝ}
    {c : ℝ≥0∞} {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    (he : μ=c • volume.withDensity (gibbsDensity H)) : μ=gibbs H := by
  have hh := congrArg (fun ν : Measure (Point d) => ν Set.univ) he
  rw [measure_univ,Measure.smul_apply,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,smul_eq_mul] at hh
  have hc : c=(partition H)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left hh.symm
  simpa [gibbs,hc] using he

def interpolationLaw {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ) : Measure (Point d) :=
  ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).map
    (fun p => ρ • p.1+Real.sqrt (1-ρ^2) • p.2)

lemma interpolation_exponent {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r ρ : ℝ) (y z : Point d) (ha : 1-ρ^2≠0) :
    -primitivePotential F x r z-‖y-ρ • z‖^2/(2*(1-ρ^2))=
      -‖y‖^2/(2*(1-ρ^2))+
        (inner ℝ (conditionalParameter (ρ,y)).1 z-
          (conditionalParameter (ρ,y)).2*‖z‖^2-primitivePotential F x r z) := by
  simp only [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    inner_smul_right,inner_smul_left,conditionalParameter,conj_trivial]
  rw [real_inner_comm z y]
  field_simp
  ring

lemma interpolation_density_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2<1) (hρ : ρ^2<1) (y : Point d) :
    (∫⁻ z,ENNReal.ofReal (Real.exp (-primitivePotential F x r z-
      ‖y-ρ • z‖^2/(2*(1-ρ^2)))))=gibbsDensity (interpolationPotential F x r ρ) y := by
  obtain ⟨m,hm,C,ht⟩ := hF.hasGaussianLowerTail x hr hl
  let p := conditionalParameter (ρ,y)
  have hp : 0 < m+p.2 := by dsimp [p,conditionalParameter]; positivity
  have hi := integrable_quadraticTilt (hF.continuous_potential x r) continuous_const ht
    (growth_const (1:ℝ)) p hp
  have hz := quadratic_partition_pos (hF.continuous_potential x r) ht p hp
  have he : ∀ z,Real.exp (-primitivePotential F x r z-‖y-ρ • z‖^2/(2*(1-ρ^2)))=
      Real.exp (-‖y‖^2/(2*(1-ρ^2)))*
        Real.exp (inner ℝ p.1 z-p.2*‖z‖^2-primitivePotential F x r z) := by
    intro z
    rw [interpolation_exponent F x r ρ y z (by linarith),Real.exp_add]
  simp_rw [he,ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hH := (hF.continuous_potential x r).measurable
  rw [lintegral_const_mul _ (by fun_prop)]
  have ht' : (∫⁻ z, ENNReal.ofReal (Real.exp (inner ℝ p.1 z-p.2*‖z‖^2-
      primitivePotential F x r z)))=ENNReal.ofReal (quadraticTilt (primitivePotential F x r) (fun _ => (1:ℝ)) p) := by
    dsimp [quadraticTilt]
    simp only [smul_eq_mul,mul_one] at hi ⊢
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
      hi.aestronglyMeasurable,ENNReal.ofReal_toReal
        ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
          (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).2 hi)]
  rw [ht',←ENNReal.ofReal_mul (Real.exp_pos _).le]
  unfold gibbsDensity interpolationPotential
  congr 1
  rw [neg_sub,Real.exp_sub,Real.exp_log hz]
  dsimp [p]
  rw [neg_div,Real.exp_neg]
  ring

lemma interpolationLaw_probability {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2<1) (ρ : ℝ) : IsProbabilityMeasure (interpolationLaw F x r ρ) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl))
  unfold interpolationLaw
  infer_instance

theorem interpolationLaw_eq_gibbs {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2<1) (hρ : ρ^2<1) :
    interpolationLaw F x r ρ=gibbs (interpolationPotential F x r ρ) := by
  let := interpolationLaw_probability hF x hr hl ρ
  apply probability_density_eq_gibbs
  have ha : 0 < 1-ρ^2 := by linarith
  have hσ : Real.sqrt (1-ρ^2)≠0 := (Real.sqrt_pos.mpr ha).ne'
  have hd := EulerDensity.joint_density (hF.continuous_potential x r).measurable
    (fun z => ρ • z) (by fun_prop) hσ
  have he : interpolationLaw F x r ρ=
      (((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).map
        (fun p => (p.1,ρ • p.1+Real.sqrt (1-ρ^2) • p.2))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (by fun_prop)]
    rfl
  rw [he,hd,Measure.map_smul _ measurable_snd.aemeasurable,map_snd_withDensity _ _ (by
    have := (hF.continuous_potential x r).measurable
    fun_prop)]
  congr 1
  congr 1
  funext y
  simp only [Real.sq_sqrt ha.le]
  exact interpolation_density_integral hF x hr hl hρ y
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
