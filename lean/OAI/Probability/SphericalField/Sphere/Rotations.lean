import Mathlib
import OAI.Probability.SphericalField.Sphere.Invariance
import OAI.Probability.SphericalField.Perceptron.TimeLaw

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
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

end SphericalPerceptron
end
end
end

end OAI
