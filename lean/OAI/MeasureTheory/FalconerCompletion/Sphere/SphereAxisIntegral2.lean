import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Fourier.SphereNorthSchwartz2
import OAI.MeasureTheory.FalconerCompletion.Sphere.SpherePlaneWave3

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def sphereAxisIntegralND (Λ : ℝ) (e : V) (b : V → ℂ) : ℂ :=
  ∫ w, Complex.exp (Complex.I*Λ*(inner ℝ w e : ℂ))*b w ∂canonicalSphereMeasureND V

lemma sphereAxisIntegralND_rotate (R : V ≃ₗᵢ[ℝ] V) (Λ : ℝ) (v : V) (b : V → ℂ) :
    sphereAxisIntegralND Λ (R v) b = sphereAxisIntegralND Λ v (b ∘ R) := by
  unfold sphereAxisIntegralND
  rw [← integral_canonicalSphereMeasureND_isometry R]
  simp only [LinearIsometryEquiv.inner_map_map,Function.comp_def]

omit [MeasurableSpace V] [BorelSpace V] in
noncomputable def sphereAxisReflectionND (v e : V) : V ≃ₗᵢ[ℝ] V :=
  Submodule.reflection (ℝ ∙ (v-e))ᗮ

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma sphereAxisReflectionND_apply {v e : V} (he : ‖v‖ = ‖e‖) :
    sphereAxisReflectionND v e v = e := Submodule.reflection_sub he

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set Metric
open scoped ContDiff SchwartzMap RealInnerProductSpace
variable {n : ℕ}

lemma sphere_north_normND :
    ‖(WithLp.toLp 2 (0,(1:ℝ)) : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))‖ = 1 := by
  have h := sphereChartND_norm (V := EuclideanSpace ℝ (Fin n)) (u := 0) (by simp)
  rwa [sphereChartND_north] at h

theorem sphere_rotated_stationaryND_uniform (C : ℝ) (hC : 0 ≤ C) (J : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ)
      (A Λ : ℝ) (e : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))
      (hb : ContDiff ℝ ∞ b), 1 ≤ A → 0 < Λ → ‖e‖ = 1 →
      (∀ j ≤ 2*(J+1)+n+3, ∀ w, ‖w‖ = 1 → ‖iteratedFDeriv ℝ j b w‖ ≤ C*A^j) →
      let R := sphereAxisReflectionND (WithLp.toLp 2 (0,(1:ℝ))) e
      let b' := b ∘ R
      let hb' := hb.comp R.toContinuousLinearEquiv.contDiff
      ‖sphereAxisIntegralND Λ e b -
        (Complex.exp (Complex.I * Λ) *
          (fresnelCoefficientND (EuclideanSpace ℝ (Fin n)) (Λ/2) *
            quadraticExpansionND (sphereNorthSchwartzND b' hb') J (Λ/2)) +
        star (Complex.exp (Complex.I * Λ) *
          (fresnelCoefficientND (EuclideanSpace ℝ (Fin n)) (Λ/2) *
            quadraticExpansionND (sphereSouthSchwartzND b' hb') J (Λ/2))))‖ ≤
        D * Λ^(-(n:ℝ)/2-(J+1:ℕ)) * A^(2*(J+1)+n+3) := by
  obtain ⟨D,hD,hfull⟩ := sphere_full_stationaryND_uniform (n := n) C hC J
  refine ⟨D,hD,?_⟩
  intro b A Λ e hb hA hΛ he hderiv
  dsimp only
  let R := sphereAxisReflectionND (WithLp.toLp 2 (0,(1:ℝ))) e
  have hR : R (WithLp.toLp 2 (0,(1:ℝ))) = e :=
    sphereAxisReflectionND_apply (sphere_north_normND.trans he.symm)
  have hrot : sphereAxisIntegralND Λ e b = sphereOscillationND Λ (b ∘ R) := by
    rw [← hR,sphereAxisIntegralND_rotate]
    rfl
  rw [hrot]
  apply hfull (b ∘ R) A Λ (hb.comp R.toContinuousLinearEquiv.contDiff) hA hΛ
  intro j hj w hw
  rw [R.norm_iteratedFDeriv_comp_right]
  exact hderiv j hj (R w) (by simpa using hw)

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

instance canonicalSphereMeasureND_finite : IsFiniteMeasure (canonicalSphereMeasureND V) := by
  unfold canonicalSphereMeasureND
  infer_instance

lemma canonicalSphereMeasureND_ae_norm :
    ∀ᵐ w ∂canonicalSphereMeasureND V, ‖w‖ = 1 := by
  rw [canonicalSphereMeasureND, ae_map_iff measurable_subtype_coe.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet]
  exact Filter.Eventually.of_forall (fun w => by simp)

omit [MeasurableSpace V] [BorelSpace V] in
noncomputable def skewFlowND (A : V →L[ℝ] V) (hA : star A = -A) (t : ℝ) : V ≃ₗᵢ[ℝ] V := by
  letI : NormedAlgebra ℚ (V →L[ℝ] V) := .restrictScalars ℚ ℝ (V →L[ℝ] V)
  exact Unitary.linearIsometryEquiv ⟨NormedSpace.exp (t • A),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
      rw [skewAdjoint.mem_iff,star_smul,hA]
      simp)⟩

omit [MeasurableSpace V] [BorelSpace V] in
lemma skewFlowND_apply (A : V →L[ℝ] V) (hA : star A = -A) (t : ℝ) (w : V) :
    skewFlowND A hA t w = NormedSpace.exp (t • A) w := rfl

omit [MeasurableSpace V] [BorelSpace V] in
lemma skewFlowND_zero (A : V →L[ℝ] V) (hA : star A = -A) (w : V) :
    skewFlowND A hA 0 w = w := by simp [skewFlowND_apply]

omit [MeasurableSpace V] [BorelSpace V] in
lemma skewFlowND_hasDerivAt (A : V →L[ℝ] V) (hA : star A = -A) (t : ℝ) (w : V) :
    HasDerivAt (fun s => skewFlowND A hA s w) (A (skewFlowND A hA t w)) t := by
  simpa only [skewFlowND_apply, mul_apply_eq_comp,
    ContinuousLinearMap.map_zero,add_zero] using
    (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t w)

theorem integral_sphere_skew_derivative_zero (A : V →L[ℝ] V) (hA : star A = -A)
    {f : V → ℂ} (hf : ContDiff ℝ ∞ f) :
    (∫ w, fderiv ℝ f w (A w) ∂canonicalSphereMeasureND V) = 0 := by
  let F : ℝ → V → ℂ := fun t w => f (skewFlowND A hA t w)
  let F' : ℝ → V → ℂ := fun t w =>
    fderiv ℝ f (skewFlowND A hA t w) (A (skewFlowND A hA t w))
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  obtain ⟨C,hC⟩ := (isCompact_sphere (0:V) 1).exists_bound_of_continuousOn hdf.continuousOn
  have hF' (t : ℝ) : Continuous (F' t) := by
    dsimp [F']
    exact (hdf.comp (skewFlowND A hA t).continuous).clm_apply
      (A.continuous.comp (skewFlowND A hA t).continuous)
  have hbound : ∀ᵐ w ∂canonicalSphereMeasureND V, ∀ t ∈ (Set.univ : Set ℝ),
      ‖F' t w‖ ≤ C*‖A‖ := by
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw t _
    have hx : ‖skewFlowND A hA t w‖ = 1 := by simpa using hw
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    calc
      ‖fderiv ℝ f (skewFlowND A hA t w)‖ * ‖A (skewFlowND A hA t w)‖ ≤
          ‖fderiv ℝ f (skewFlowND A hA t w)‖ * ‖A‖ :=
        mul_le_mul_of_nonneg_left (by simpa [hx] using A.le_opNorm (skewFlowND A hA t w)) (norm_nonneg _)
      _ ≤ C*‖A‖ := mul_le_mul_of_nonneg_right
        (hC _ (by simpa using hx)) (norm_nonneg _)
  have hdiff : ∀ᵐ w ∂canonicalSphereMeasureND V, ∀ t ∈ (Set.univ : Set ℝ),
      HasDerivAt (F · w) (F' t w) t := by
    filter_upwards [] with w t _
    exact (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      (skewFlowND_hasDerivAt A hA t w)
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (x₀ := (0:ℝ)) (μ := canonicalSphereMeasureND V) (F := F) (F' := F')
    (bound := fun _ => C*‖A‖) Filter.univ_mem
    (Filter.Eventually.of_forall (fun t =>
      ((hf.continuous.comp (skewFlowND A hA t).continuous).aestronglyMeasurable)))
    (integrable_canonicalSphereMeasureND (hf.continuous.comp (skewFlowND A hA 0).continuous))
    (hF' 0).aestronglyMeasurable hbound (integrable_const _) hdiff
  have he : (fun t => ∫ w, F t w ∂canonicalSphereMeasureND V) =
      (fun _ : ℝ => ∫ w, f w ∂canonicalSphereMeasureND V) := by
    funext t
    exact integral_canonicalSphereMeasureND_isometry (skewFlowND A hA t) f
  have hz := hparam.2
  rw [he] at hz
  have hh := hz.unique (hasDerivAt_const (0:ℝ) (∫ w, f w ∂canonicalSphereMeasureND V))
  simpa [F',skewFlowND_zero] using hh

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
noncomputable def angularDerivativeND (A : V →L[ℝ] V) (f : V → ℂ) (x : V) : ℂ :=
  fderiv ℝ f x (A x)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_contDiff (A : V →L[ℝ] V) {f : V → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (angularDerivativeND A f) :=
  (hf.fderiv_right (by simp)).clm_apply A.contDiff

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_mul (A : V →L[ℝ] V) {f g : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : V) :
    angularDerivativeND A (fun w => f w*g w) x =
      angularDerivativeND A f x*g x + f x*angularDerivativeND A g x := by
  unfold angularDerivativeND
  change (fderiv ℝ (f*g) x) (A x) = _
  rw [fderiv_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp [mul_comm,add_comm]

lemma sphere_angular_integration_by_parts (A : V →L[ℝ] V) (hA : star A = -A)
    {f g : V → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    (∫ w, angularDerivativeND A f w*g w ∂canonicalSphereMeasureND V) =
      -(∫ w, f w*angularDerivativeND A g w ∂canonicalSphereMeasureND V) := by
  have hz := integral_sphere_skew_derivative_zero A hA (hf.mul hg)
  change (∫ w, angularDerivativeND A (fun w => f w*g w) w ∂canonicalSphereMeasureND V) = 0 at hz
  simp_rw [angularDerivativeND_mul A hf hg] at hz
  rw [integral_add (f := fun w => angularDerivativeND A f w*g w)
    (g := fun w => f w*angularDerivativeND A g w)
    (integrable_canonicalSphereMeasureND ((angularDerivativeND_contDiff A hf).continuous.mul hg.continuous))
    (integrable_canonicalSphereMeasureND (hf.continuous.mul (angularDerivativeND_contDiff A hg).continuous))] at hz
  exact eq_neg_of_add_eq_zero_left hz

lemma sphere_angular_second_selfadjoint (A : V →L[ℝ] V) (hA : star A = -A)
    {f g : V → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    (∫ w, angularDerivativeND A (angularDerivativeND A f) w*g w ∂canonicalSphereMeasureND V) =
      ∫ w, f w*angularDerivativeND A (angularDerivativeND A g) w ∂canonicalSphereMeasureND V := by
  rw [sphere_angular_integration_by_parts A hA (angularDerivativeND_contDiff A hf) hg,
    sphere_angular_integration_by_parts A hA hf (angularDerivativeND_contDiff A hg), neg_neg]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
noncomputable def angularGeneratorND (v w : V) : V →L[ℝ] V :=
  InnerProductSpace.rankOne ℝ w v - InnerProductSpace.rankOne ℝ v w

omit [MeasurableSpace V] [BorelSpace V] in
lemma angularGeneratorND_skew (v w : V) :
    star (angularGeneratorND v w) = -angularGeneratorND v w := by
  simp [angularGeneratorND,ContinuousLinearMap.star_eq_adjoint]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularGeneratorND_apply (v w x : V) :
    angularGeneratorND v w x = inner ℝ v x • w - inner ℝ w x • v := by
  simp [angularGeneratorND,InnerProductSpace.rankOne_apply]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
noncomputable def spherePlaneWaveND (Λ : ℝ) (e x : V) : ℂ :=
  Complex.exp (Complex.I*Λ*(inner ℝ x e : ℂ))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma spherePlaneWaveND_contDiff (Λ : ℝ) (e : V) :
    ContDiff ℝ ∞ (spherePlaneWaveND Λ e) := by
  unfold spherePlaneWaveND
  have hi : ContDiff ℝ ∞ (fun x : V => (inner ℝ x e : ℂ)) :=
    by simpa [Function.comp_def,real_inner_comm] using
      Complex.ofRealCLM.contDiff.comp (innerSL ℝ e).contDiff
  exact (contDiff_const.mul hi).cexp

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_planeWave (A : V →L[ℝ] V) (Λ : ℝ) (e x : V) :
    angularDerivativeND A (spherePlaneWaveND Λ e) x =
      spherePlaneWaveND Λ e x * (Complex.I*Λ*(inner ℝ (A x) e : ℂ)) := by
  let L : V →L[ℝ] ℂ := Complex.ofRealCLM.comp (innerSL ℝ e)
  have hL : ∀ w, L w = (inner ℝ w e : ℂ) := by
    intro w
    simp [L,real_inner_comm]
  have h := ((L.hasFDerivAt (x := x)).const_mul (Complex.I*Λ)).cexp
  change HasFDerivAt _ _ x at h
  unfold angularDerivativeND spherePlaneWaveND
  have he : (fun y => Complex.exp (Complex.I*Λ*L y)) =
      (fun y => Complex.exp (Complex.I*Λ*(inner ℝ y e : ℂ))) := by ext y; rw [hL]
  rw [he] at h
  rw [h.fderiv]
  simp [hL,smul_eq_mul]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_complexLinear (A : V →L[ℝ] V) (L : V →L[ℝ] ℂ)
    (c : ℂ) (x : V) :
    angularDerivativeND A (fun w => c*L w) x = c*L (A x) := by
  unfold angularDerivativeND
  rw [((L.hasFDerivAt (x := x)).const_mul c).fderiv]
  simp

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_planeWave_second (A : V →L[ℝ] V) (Λ : ℝ) (e x : V) :
    angularDerivativeND A (angularDerivativeND A (spherePlaneWaveND Λ e)) x =
      spherePlaneWaveND Λ e x *
        (- (Λ:ℂ)^2*(inner ℝ (A x) e : ℂ)^2 +
          Complex.I*Λ*(inner ℝ (A (A x)) e : ℂ)) := by
  let L : V →L[ℝ] ℂ := (Complex.ofRealCLM.comp (innerSL ℝ e)).comp A
  have hL : ∀ w, L w = (inner ℝ (A w) e : ℂ) := by
    intro w
    simp [L,real_inner_comm]
  have he : angularDerivativeND A (spherePlaneWaveND Λ e) =
      fun w => spherePlaneWaveND Λ e w * (Complex.I*Λ*L w) := by
    ext w
    rw [angularDerivativeND_planeWave,hL]
  have hsm : ContDiff ℝ ∞ (fun w => Complex.I*Λ*L w) := contDiff_const.mul L.contDiff
  rw [he,angularDerivativeND_mul A (spherePlaneWaveND_contDiff Λ e) hsm,
    angularDerivativeND_planeWave,angularDerivativeND_complexLinear,hL,hL]
  ring_nf
  rw [Complex.I_sq]
  ring

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
