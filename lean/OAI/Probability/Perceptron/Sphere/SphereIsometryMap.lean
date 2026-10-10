import Mathlib
import OAI.Probability.Perceptron.Variational.StableLogIntensity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
section SphereInvariance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sphereIsometryMap (e : E ≃ₗᵢ[ℝ] E) (x : Metric.sphere (0 : E) 1) :
    Metric.sphere (0 : E) 1 := ⟨e x, by simp⟩

omit [FiniteDimensional ℝ E] in
lemma sphereIsometryMap_measurable (e : E ≃ₗᵢ[ℝ] E) : Measurable (sphereIsometryMap e) :=
  (e.continuous.comp continuous_subtype_val).subtype_mk _ |>.measurable

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sphereIsometryMap_preimage_cone (e : E ≃ₗᵢ[ℝ] E) (s : Set (Metric.sphere (0 : E) 1)) :
    Ioo (0:ℝ) 1 • (Subtype.val '' (sphereIsometryMap e ⁻¹' s)) =
      e ⁻¹' (Ioo (0:ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r,hr,v,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨r,hr,e u,⟨sphereIsometryMap e u,hu,rfl⟩,by simp⟩
  · rintro ⟨r,hr,v,⟨u,hu,rfl⟩,he⟩
    refine ⟨r,hr,e.symm u,⟨sphereIsometryMap e.symm u,?_,rfl⟩,?_⟩
    · simpa [sphereIsometryMap] using hu
    · apply e.injective
      simpa only [map_smul,LinearIsometryEquiv.apply_symm_apply] using he

lemma sphereIsometryMap_preserving (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereIsometryMap e) (volume : Measure E).toSphere (volume : Measure E).toSphere := by
  refine ⟨sphereIsometryMap_measurable e,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereIsometryMap_measurable e) hs,
    Measure.toSphere_apply' _ ((sphereIsometryMap_measurable e) hs),Measure.toSphere_apply' _ hs,
    sphereIsometryMap_preimage_cone]
  congr 1
  exact e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding _

end SphereInvariance

lemma unitSphereLaw_isometry_preserving {N : ℕ} (e : Spin N ≃ₗᵢ[ℝ] Spin N) :
    MeasurePreserving (sphereIsometryMap e) (unitSphereLaw N) (unitSphereLaw N) := by
  refine ⟨sphereIsometryMap_measurable e,?_⟩
  unfold unitSphereLaw
  rw [Measure.map_smul _ (sphereIsometryMap_measurable e).aemeasurable,
    (sphereIsometryMap_preserving e).map_eq]

lemma sphereLaw_isometry_preserving {N : ℕ} (e : Spin N ≃ₗᵢ[ℝ] Spin N) :
    MeasurePreserving e (sphereLaw N) (sphereLaw N) := by
  refine ⟨e.continuous.measurable,?_⟩
  have hm : Measurable (fun x : Metric.sphere (0 : Spin N) 1 => Real.sqrt (N:ℝ) • x.val) :=
    (continuous_subtype_val.const_smul (Real.sqrt (N:ℝ))).measurable
  rw [sphereLaw,Measure.map_map e.continuous.measurable hm]
  have hc : (e ∘ fun x : Metric.sphere (0 : Spin N) 1 => Real.sqrt (N:ℝ) • x.val) =
      (fun x : Metric.sphere (0 : Spin N) 1 => Real.sqrt (N:ℝ) • x.val) ∘ sphereIsometryMap e := by
    funext x
    exact e.map_smul _ _
  rw [hc]
  rw [← Measure.map_map hm (sphereIsometryMap_measurable e),
    (unitSphereLaw_isometry_preserving e).map_eq]

section RotationCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def skewFlow (A : E →L[ℝ] E) (hA : A ∈ skewAdjoint (E →L[ℝ] E)) (t : ℝ) : E ≃ₗᵢ[ℝ] E := by
  letI : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)
  exact Unitary.linearIsometryEquiv ⟨NormedSpace.exp (t • A),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
      rw [skewAdjoint.mem_iff] at hA ⊢
      simp [hA])⟩

lemma skewFlow_apply (A : E →L[ℝ] E) (hA : A ∈ skewAdjoint (E →L[ℝ] E)) (t : ℝ) (x : E) :
    skewFlow A hA t x = NormedSpace.exp (t • A) x := rfl

lemma skewFlow_zero (A : E →L[ℝ] E) (hA : A ∈ skewAdjoint (E →L[ℝ] E)) (x : E) :
    skewFlow A hA 0 x = x := by simp [skewFlow_apply]

lemma skewFlow_deriv (A : E →L[ℝ] E) (hA : A ∈ skewAdjoint (E →L[ℝ] E)) (t : ℝ) (x : E) :
    HasDerivAt (fun u => skewFlow A hA u x) (A (skewFlow A hA t x)) t := by
  simpa only [skewFlow_apply,mul_apply_eq_comp,map_zero,
    add_zero] using (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t x)

variable [MeasurableSpace E] [BorelSpace E]

lemma integrable_of_continuous_sphere_support (μ : Measure E) [IsFiniteMeasure μ] {R : ℝ}
    (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R) {f : E → ℝ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E) R).exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (hR.mono fun x hx =>
    hC x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx))

lemma invariant_skew_integral_zero (μ : Measure E) [IsFiniteMeasure μ] {R : ℝ}
    (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R) (A : E →L[ℝ] E) (hA : A ∈ skewAdjoint (E →L[ℝ] E))
    (hμ : ∀ t, MeasurePreserving (skewFlow A hA t) μ μ) {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    ∫ x, fderiv ℝ f x (A x) ∂μ = 0 := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E) R).exists_bound_of_continuousOn
    (hf.continuous_fderiv (by norm_num)).continuousOn
  have hDf (t : ℝ) : Continuous (fun x => fderiv ℝ f (skewFlow A hA t x) (A (skewFlow A hA t x))) :=
    ((hf.continuous_fderiv (by norm_num)).comp (skewFlow A hA t).continuous).clm_apply
      (A.continuous.comp (skewFlow A hA t).continuous)
  have hder := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Set.univ) (x₀ := (0:ℝ))
    (F := fun t x => f (skewFlow A hA t x))
    (F' := fun t x => fderiv ℝ f (skewFlow A hA t x) (A (skewFlow A hA t x)))
    (bound := fun _ => max C 0 * (‖A‖ * R)) (Filter.univ_mem)
    (Filter.Eventually.of_forall fun t => (hf.continuous.comp (skewFlow A hA t).continuous).aestronglyMeasurable)
    (integrable_of_continuous_sphere_support μ hR (hf.continuous.comp (skewFlow A hA 0).continuous))
    ((hDf 0).aestronglyMeasurable) (hR.mono fun x hx t _ => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun x t _ =>
      (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (skewFlow_deriv A hA t x))).2
  · have hconst (t : ℝ) : (∫ x, f (skewFlow A hA t x) ∂μ) = ∫ x, f x ∂μ :=
      (hμ t).integral_comp (skewFlow A hA t).toHomeomorph.measurableEmbedding f
    have hc : HasDerivAt (fun t : ℝ => ∫ x, f (skewFlow A hA t x) ∂μ) 0 0 := by
      simp_rw [hconst]
      exact hasDerivAt_const _ _
    simpa only [skewFlow_zero] using hder.unique hc
  · have hb : ‖fderiv ℝ f (skewFlow A hA t x)‖ ≤ max C 0 :=
      (hC _ (by simpa only [Metric.mem_closedBall,dist_zero_right,LinearIsometryEquiv.norm_map] using hx)).trans (le_max_left _ _)
    calc
      ‖fderiv ℝ f (skewFlow A hA t x) (A (skewFlow A hA t x))‖ ≤
          ‖fderiv ℝ f (skewFlow A hA t x)‖ * ‖A (skewFlow A hA t x)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ max C 0 * (‖A‖ * R) := mul_le_mul hb
        ((A.le_opNorm _).trans (by rw [LinearIsometryEquiv.norm_map]; gcongr)) (norm_nonneg _) (le_max_right _ _)

noncomputable def planeSkew (a y : E) : E →L[ℝ] E :=
  InnerProductSpace.rankOne ℝ a y - InnerProductSpace.rankOne ℝ y a

omit [MeasurableSpace E] [BorelSpace E] in
lemma planeSkew_mem (a y : E) : planeSkew a y ∈ skewAdjoint (E →L[ℝ] E) := by
  rw [skewAdjoint.mem_iff,planeSkew,star_sub,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.star_eq_adjoint,InnerProductSpace.adjoint_rankOne,InnerProductSpace.adjoint_rankOne]
  abel

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma planeSkew_apply (a y x : E) : planeSkew a y x = inner ℝ y x • a - inner ℝ a x • y := by
  simp [planeSkew,InnerProductSpace.rankOne_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rotation_product_deriv {f : E → ℝ} (hf : ContDiff ℝ 1 f) (a y x : E) :
    fderiv ℝ (fun z => inner ℝ a z * f z) x (planeSkew a y x) =
      inner ℝ a (planeSkew a y x) * f x + inner ℝ a x * fderiv ℝ f x (planeSkew a y x) := by
  have hh := ((innerSL ℝ a).hasFDerivAt.mul (hf.differentiable (by norm_num) x).hasFDerivAt).fderiv
  have hh' : fderiv ℝ (fun z => inner ℝ a z * f z) x =
      (inner ℝ a x) • fderiv ℝ f x + f x • (innerSL ℝ a) := by
    simpa only [Pi.mul_def,coe_innerSL_apply,innerSL_apply_apply] using hh
  rw [hh']
  simp [mul_comm,add_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sum_planeSkew (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x y : E) :
    ∑ i, inner ℝ (b i) x • planeSkew (b i) y x =
      inner ℝ y x • x - (‖x‖^2) • y := by
  have hn : ∑ i, (inner ℝ (b i) x)^2 = ‖x‖^2 := by
    simpa only [real_inner_comm x,pow_two,real_inner_self_eq_norm_sq] using b.sum_inner_mul_inner x x
  simp_rw [planeSkew_apply,smul_sub,smul_smul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · calc
      _ = ∑ i, inner ℝ y x • (inner ℝ (b i) x • b i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul,mul_comm]
      _ = _ := by rw [← Finset.smul_sum,b.sum_repr' x]
  · rw [← Finset.sum_smul,← hn]
    simp only [pow_two]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sum_planeSkew_divergence (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x y : E) :
    ∑ i, inner ℝ (b i) (planeSkew (b i) y x) = (Fintype.card ι - 1 : ℝ) * inner ℝ y x := by
  simp_rw [planeSkew_apply,inner_sub_right,inner_smul_right,b.inner_eq_one,mul_one]
  rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hb : (∑ i, inner ℝ (b i) x * inner ℝ (b i) y) = inner ℝ y x := by
    calc
      _ = ∑ i, inner ℝ y (b i) * inner ℝ (b i) x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm y (b i),mul_comm]
      _ = _ := b.sum_inner_mul_inner y x
  rw [hb]
  ring

lemma invariant_tangent_integral (μ : Measure E) [IsFiniteMeasure μ] {R : ℝ}
    (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R) (hμ : ∀ e : E ≃ₗᵢ[ℝ] E, MeasurePreserving e μ μ)
    (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ E) (y : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    ∫ x, fderiv ℝ f x ((‖x‖^2) • y - inner ℝ y x • x) ∂μ =
      ∫ x, (Fintype.card ι - 1 : ℝ) * inner ℝ y x * f x ∂μ := by
  let F : ι → E → ℝ := fun i x => inner ℝ (b i) x * f x
  have hF (i) : ContDiff ℝ 1 (F i) := (innerSL ℝ (b i)).contDiff.mul hf
  have hI (i) : Integrable (fun x => fderiv ℝ (F i) x (planeSkew (b i) y x)) μ :=
    integrable_of_continuous_sphere_support μ hR
      (((hF i).continuous_fderiv (by norm_num)).clm_apply (planeSkew (b i) y).continuous)
  have hzero (i) := invariant_skew_integral_zero μ hR (planeSkew (b i) y) (planeSkew_mem _ _)
    (fun t => hμ (skewFlow _ (planeSkew_mem _ _) t)) (hF i)
  have halg (x) : (∑ i, fderiv ℝ (F i) x (planeSkew (b i) y x)) =
      (Fintype.card ι - 1 : ℝ) * inner ℝ y x * f x -
        fderiv ℝ f x ((‖x‖^2) • y - inner ℝ y x • x) := by
    simp_rw [F,rotation_product_deriv hf,Finset.sum_add_distrib]
    rw [← Finset.sum_mul,sum_planeSkew_divergence]
    have hh : (∑ i, inner ℝ (b i) x * fderiv ℝ f x (planeSkew (b i) y x)) =
        fderiv ℝ f x (inner ℝ y x • x - (‖x‖^2) • y) := by
      rw [← sum_planeSkew ι b x y,map_sum]
      simp only [map_smul,smul_eq_mul]
    rw [hh,map_sub,map_sub]
    ring
  have hi₁ := integrable_of_continuous_sphere_support μ hR
    (show Continuous (fun x => (Fintype.card ι - 1 : ℝ)*inner ℝ y x*f x) by fun_prop)
  have hi₂ := integrable_of_continuous_sphere_support μ hR
    (show Continuous (fun x => fderiv ℝ f x ((‖x‖^2) • y - inner ℝ y x • x)) from
      (hf.continuous_fderiv (by norm_num)).clm_apply (by fun_prop))
  have he : (∫ x, (Fintype.card ι - 1 : ℝ)*inner ℝ y x*f x ∂μ) -
      (∫ x, fderiv ℝ f x ((‖x‖^2) • y - inner ℝ y x • x) ∂μ) = 0 := by
    rw [← integral_sub hi₁ hi₂]
    simp_rw [← halg]
    rw [integral_finsetSum _ (fun i _ => hI i)]
    simp only [hzero,Finset.sum_const_zero]
  linarith

end RotationCalculus
lemma sphereLaw_ae_norm (N : ℕ) : ∀ᵐ x ∂sphereLaw N, ‖x‖ = Real.sqrt (N:ℝ) := by
  have hm : Measurable (fun x : Metric.sphere (0 : Spin N) 1 => Real.sqrt (N:ℝ) • x.val) :=
    (continuous_subtype_val.const_smul (Real.sqrt (N:ℝ))).measurable
  rw [sphereLaw,ae_map_iff hm.aemeasurable (measurableSet_eq_fun continuous_norm.measurable measurable_const)]
  exact Filter.Eventually.of_forall fun x => by
    have hx : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using x.property
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),hx,mul_one]

local instance (N : ℕ) : IsFiniteMeasure (sphereLaw N) := by
  unfold sphereLaw unitSphereLaw
  infer_instance

lemma sphere_integrable_of_continuous (N : ℕ) {f : Spin (N+1) → ℝ} (hf : Continuous f) :
    Integrable f (sphereLaw (N+1)) :=
  integrable_of_continuous_sphere_support _ ((sphereLaw_ae_norm (N+1)).mono fun _ hx => hx.le) hf

lemma sphere_tangent_integral (N : ℕ) (y : Spin (N+1)) {f : Spin (N+1) → ℝ} (hf : ContDiff ℝ 1 f) :
    ∫ x, fderiv ℝ f x (((N+1:ℕ):ℝ) • y - inner ℝ y x • x) ∂sphereLaw (N+1) =
      (N:ℝ) * ∫ x, inner ℝ y x * f x ∂sphereLaw (N+1) := by
  have hh := invariant_tangent_integral (sphereLaw (N+1))
    ((sphereLaw_ae_norm (N+1)).mono fun _ hx => hx.le) (fun e => sphereLaw_isometry_preserving e)
    (Fin (N+1)) (EuclideanSpace.basisFun (Fin (N+1)) ℝ) y hf
  calc
    _ = ∫ x, fderiv ℝ f x ((‖x‖^2) • y - inner ℝ y x • x) ∂sphereLaw (N+1) := by
      apply integral_congr_ae
      filter_upwards [sphereLaw_ae_norm (N+1)] with x hx
      rw [hx,Real.sq_sqrt (by positivity)]
    _ = _ := by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,add_sub_cancel_right,
      mul_assoc,integral_const_mul] using hh

def sphereOverlap {N : ℕ} (x y : Spin N) : ℝ := inner ℝ y x / (N:ℝ)

lemma sphere_tangent_integral_normalized (N : ℕ) (y : Spin (N+1)) {f : Spin (N+1) → ℝ}
    (hf : ContDiff ℝ 1 f) :
    ∫ x, fderiv ℝ f x (y - sphereOverlap x y • x) ∂sphereLaw (N+1) =
      (N:ℝ) * ∫ x, sphereOverlap x y * f x ∂sphereLaw (N+1) := by
  have hd : ((N+1:ℕ):ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hd
  rw [← integral_const_mul]
  have he (x : Spin (N+1)) : ((N+1:ℕ):ℝ) * fderiv ℝ f x (y - sphereOverlap x y • x) =
      fderiv ℝ f x (((N+1:ℕ):ℝ) • y - inner ℝ y x • x) := by
    rw [← smul_eq_mul,← map_smul,smul_sub,smul_smul]
    simp only [sphereOverlap,mul_div_cancel₀ _ hd]
  simp_rw [he]
  rw [sphere_tangent_integral N y hf]
  have hr : (∫ x, inner ℝ y x*f x ∂sphereLaw (N+1)) =
      ((N+1:ℕ):ℝ) * ∫ x, sphereOverlap x y * f x ∂sphereLaw (N+1) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    dsimp [sphereOverlap]
    field_simp
  rw [hr]
  ring

lemma sphereOverlap_hasFDerivAt (N : ℕ) (y x : Spin (N+1)) :
    HasFDerivAt (fun z => sphereOverlap z y) (((N+1:ℕ):ℝ)⁻¹ • innerSL ℝ y) x := by
  simpa only [sphereOverlap,Pi.smul_def,smul_eq_mul,div_eq_mul_inv,mul_comm,coe_innerSL_apply] using
    (innerSL ℝ y).hasFDerivAt.const_smul (((N+1:ℕ):ℝ)⁻¹)

lemma sphereOverlap_tangent_deriv (N : ℕ) (y : Spin (N+1)) (hy : ‖y‖^2 = ((N+1:ℕ):ℝ))
    (x : Spin (N+1)) :
    ((((N+1:ℕ):ℝ)⁻¹ • innerSL ℝ y) (y - sphereOverlap x y • x)) = 1 - sphereOverlap x y ^ 2 := by
  have hd : ((N+1:ℕ):ℝ) ≠ 0 := by positivity
  simp only [smul_apply,innerSL_apply_apply,inner_sub_right,inner_smul_right,
    real_inner_self_eq_norm_sq,hy,smul_eq_mul,sphereOverlap]
  field_simp

lemma sphere_gibbs_tangent_identity (N : ℕ) (y : Spin (N+1)) (hy : ‖y‖^2 = ((N+1:ℕ):ℝ))
    {H : Spin (N+1) → ℝ} (hH : ContDiff ℝ 1 H) {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    (N:ℝ) * (∫ x, sphereOverlap x y * (G (sphereOverlap x y) * Real.exp (H x)) ∂sphereLaw (N+1)) =
      ∫ x, (deriv G (sphereOverlap x y) * (1-sphereOverlap x y^2) +
        G (sphereOverlap x y)*fderiv ℝ H x (y-sphereOverlap x y • x))*Real.exp (H x) ∂sphereLaw (N+1) := by
  let F : Spin (N+1) → ℝ := fun x => G (sphereOverlap x y) * Real.exp (H x)
  have hR : ContDiff ℝ 1 (fun x : Spin (N+1) => sphereOverlap x y) := by
    unfold sphereOverlap
    exact (innerSL ℝ y).contDiff.div_const _
  have hF : ContDiff ℝ 1 F := (hG.comp hR).mul hH.exp
  rw [← sphere_tangent_integral_normalized N y hF]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have hh := (((hG.differentiable (by norm_num) (sphereOverlap x y)).hasDerivAt.comp_hasFDerivAt x
      (sphereOverlap_hasFDerivAt N y x)).mul (hH.differentiable (by norm_num) x).hasFDerivAt.exp).fderiv
    have he : fderiv ℝ F x = G (sphereOverlap x y) • (Real.exp (H x) • fderiv ℝ H x) +
        Real.exp (H x) • (deriv G (sphereOverlap x y) • (((N+1:ℕ):ℝ)⁻¹ • innerSL ℝ y)) := by
      simpa only [F,Pi.mul_def,Function.comp_def] using hh
    dsimp only
    rw [he]
    simp only [add_apply,smul_apply,smul_eq_mul,
      sphereOverlap_tangent_deriv N y hy]
    ring

def poissonMarkMeasure {S : Type*} [MeasurableSpace S] (η : Measure (ℝ × S)) : Measure S :=
  (η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1))).map Prod.snd

def normalizedMeasure {S : Type*} [MeasurableSpace S] (μ : Measure S) : Measure S :=
  (μ univ)⁻¹ • μ

lemma measurable_measure_withDensity_fixed {S : Type*} [MeasurableSpace S]
    {f : S → ℝ≥0∞} (hf : Measurable f) : Measurable (fun μ : Measure S => μ.withDensity f) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [withDensity_apply _ hs,← lintegral_indicator hs]
  exact Measure.measurable_lintegral (hf.indicator hs)

lemma poissonMarkMeasure_measurable {S : Type*} [MeasurableSpace S] :
    Measurable (poissonMarkMeasure (S := S)) :=
  (Measure.measurable_map _ measurable_snd).comp
    (measurable_measure_withDensity_fixed (by fun_prop))

lemma normalizedMeasure_measurable {S : Type*} [MeasurableSpace S] :
    Measurable (normalizedMeasure (S := S)) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  change Measurable (fun μ : Measure S => (μ univ)⁻¹ * μ s)
  exact (Measure.measurable_coe MeasurableSet.univ).inv.mul (Measure.measurable_coe hs)

lemma normalizedMeasure_probability {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (h0 : μ univ ≠ 0) (hf : μ univ ≠ ⊤) : IsProbabilityMeasure (normalizedMeasure μ) := by
  constructor
  change (μ univ)⁻¹ * μ univ = 1
  exact ENNReal.inv_mul_cancel h0 hf

lemma normalizedMeasure_smul {S : Type*} [MeasurableSpace S] (μ : Measure S)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcf : c ≠ ⊤) :
    normalizedMeasure (c • μ) = normalizedMeasure μ := by
  unfold normalizedMeasure
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.mul_inv (Or.inl hc0) (Or.inl hcf),smul_smul]
  congr 1
  calc
    c⁻¹ * (μ univ)⁻¹ * c = c⁻¹*c*(μ univ)⁻¹ := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hc0 hcf,one_mul]

lemma map_withDensity_comp {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) {f : S → T} (hf : Measurable f) {g : T → ℝ≥0∞} (hg : Measurable g) :
    (μ.map f).withDensity g = (μ.withDensity (g ∘ f)).map f := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_withDensity_eq_lintegral_mul _ hg hh,
    lintegral_map (hg.mul hh) hf,lintegral_map hh hf]
  rw [lintegral_withDensity_eq_lintegral_mul _ (hg.comp hf) (show Measurable (fun x => h (f x)) from hh.comp hf)]
  rfl

lemma poissonMarkMeasure_shift {S : Type*} [MeasurableSpace S]
    (η : Measure (ℝ × S)) {F : S → ℝ} (hF : Measurable F) :
    poissonMarkMeasure (η.map (logMarkShift F)) =
      (poissonMarkMeasure η).withDensity (fun s => ENNReal.ofReal (Real.exp (F s))) := by
  unfold poissonMarkMeasure
  rw [map_withDensity_comp _ (logMarkShift_measurable hF) (by fun_prop),
    Measure.map_map measurable_snd (logMarkShift_measurable hF),
    map_withDensity_comp _ measurable_snd (by fun_prop),← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  congr 1
  funext p
  simp only [Function.comp_def,logMarkShift,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le,Pi.mul_apply]

lemma poissonMarkMeasure_mass {S : Type*} [MeasurableSpace S] (η : Measure (ℝ × S)) :
    poissonMarkMeasure η univ = ∫⁻ p, ENNReal.ofReal (Real.exp p.1) ∂η := by
  unfold poissonMarkMeasure
  rw [Measure.map_apply measurable_snd MeasurableSet.univ]
  simp only [preimage_univ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]

lemma poissonMarkMeasure_probability {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν),
      IsProbabilityMeasure (normalizedMeasure (poissonMarkMeasure η)) := by
  have he : (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map (Measure.map Prod.fst) =
      poissonRandomMeasureLaw (stableLogIntensity b) := by
    rw [poissonRandomMeasureLaw_map _ measurable_fst]
    simp only [Measure.map_fst_prod,measure_univ,one_smul]
  have hh : ∀ᵐ η ∂poissonRandomMeasureLaw (stableLogIntensity b),
      (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η) ≠ 0 ∧
      (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η) ≠ ⊤ := by
    filter_upwards [stablePoisson_total_positive hb0,stablePoisson_total_finite hb0 hb1] with η h1 h2
    exact ⟨h1.ne',h2⟩
  rw [← he] at hh
  have hmeas : Measurable (fun η : Measure ℝ => ∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η) :=
    Measure.measurable_lintegral (by fun_prop)
  have hh' := (ae_map_iff (Measure.measurable_map _ measurable_fst).aemeasurable
    (((measurableSet_eq_fun hmeas measurable_const).compl).inter
      ((measurableSet_eq_fun hmeas measurable_const).compl))).mp hh
  filter_upwards [hh'] with η hη
  change (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η.map Prod.fst) ≠ 0 ∧
    (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η.map Prod.fst) ≠ ⊤ at hη
  rw [lintegral_map (by fun_prop) measurable_fst] at hη
  exact normalizedMeasure_probability _ (by simpa only [poissonMarkMeasure_mass] using hη.1) (by simpa only [poissonMarkMeasure_mass] using hη.2)

lemma stablePoisson_gibbs_measure_law {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 ≤ b)
    {F : S → ℝ} (hF : Measurable F) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map
      (fun η => normalizedMeasure ((poissonMarkMeasure η).withDensity
        (fun s => ENNReal.ofReal (Real.exp (F s))))) =
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod
      (ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b*F s)))))).map
        (fun η => normalizedMeasure (poissonMarkMeasure η)) := by
  rw [← stablePoisson_mark_shift ν hb hF,
    Measure.map_map (show Measurable (fun η => normalizedMeasure (poissonMarkMeasure η)) from
      normalizedMeasure_measurable.comp poissonMarkMeasure_measurable)
      (show Measurable (Measure.map (logMarkShift F)) from
        Measure.measurable_map _ (logMarkShift_measurable hF))]
  congr 1
  funext η
  simp only [Function.comp_def,poissonMarkMeasure_shift η hF]

open Matrix
open scoped RealInnerProductSpace MatrixOrder

end SphericalPerceptronFreeEnergy

end

end OAI
