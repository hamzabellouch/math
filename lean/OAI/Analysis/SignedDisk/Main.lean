import OAI.Analysis.SignedDisk.CommonPrices4

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace SobolevBand
open DiskMoments RadiusEnvelope

def band (f : ℂ → ℝ) (a b : ℝ) := envelope (fun r x => signedAverage f x r) a b

lemma smooth_average_lipschitz {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a t : ℝ} (ha : 0<a) (hat : a≤t) :
    LipschitzWith (⟨(∫ y, ‖gradient f y‖)/(Real.pi*a^2),by positivity⟩ : ℝ≥0) (fun x => signedAverage f x t) := by
  obtain ⟨L,hL⟩ := hf.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  have hD := fun y => norm_fderiv_le_of_lipschitz ℝ hL (x₀ := y)
  have hi : Integrable (gradient f) := (continuous_gradient hf).integrable_of_hasCompactSupport (gradient_hasCompactSupport hc)
  have ht := ha.trans_le hat
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hasFDerivAt_signedAverage hf hD x ht).differentiableAt)
  intro x
  change ‖fderiv ℝ (fun x => signedAverage f x t) x‖ ≤ _
  rw [← (InnerProductSpace.toDual ℝ ℂ).symm.norm_map]
  change ‖gradient (fun x => signedAverage f x t) x‖ ≤ _
  rw [gradient_signedAverage hf hD x ht,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(Real.pi*t^2)⁻¹)]
  have he : ‖∫ y in Metric.ball x t, gradient f y‖ ≤ ∫ y, ‖gradient f y‖ :=
    (norm_integral_le_integral_norm _).trans (setIntegral_le_integral hi.norm (ae_of_all _ (fun y => norm_nonneg _)))
  rw [← div_eq_inv_mul]
  exact (div_le_div_of_nonneg_right he (by positivity)).trans
    (div_le_div_of_nonneg_left (integral_nonneg (fun y => norm_nonneg _)) (by positivity)
      (mul_le_mul_of_nonneg_left (sq_le_sq₀ ha.le ht.le |>.mpr hat) Real.pi_pos.le))

lemma smooth_band_lipschitz {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    LipschitzWith (⟨(∫ y, ‖gradient f y‖)/(Real.pi*a^2),by positivity⟩ : ℝ≥0) (band f a b) :=
  RadiusEnvelope.lipschitz hab (fun x => signedAverage_radius_continuousOn hf x ha)
    (fun _ hr => smooth_average_lipschitz hf hc ha hr.1)

open DiskMoments RadiusEnvelope SignedRuns GeometricFilter DyadicHats ActualLabels

lemma geometric_band_eq (f : ℂ → ℝ) (a : ℝ) (m : ℕ) :
    runEnvelope f (geometricRadii a m) 0 m = band f a (2*((2:ℝ)^m*a)) := by
  unfold runEnvelope band
  rw [geometricRadii_eq a (le_refl m),geometricRadii_eq a (Nat.zero_le m)]
  simp only [Nat.sub_self,Nat.sub_zero,scale,pow_zero,one_mul]

lemma smooth_band_integrable_gradient {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    Integrable (gradient (band f a b)) :=
  SignedDisk.LipschitzWith.integrable_gradient (smooth_band_lipschitz hf hc ha hab)
    (run_envelope_hasCompactSupport hf hc ha hab)

lemma smooth_dyadic_bound : ∃ C : ℝ, 0<C ∧ ∀ {f : ℂ → ℝ}, ContDiff ℝ 1 f →
    HasCompactSupport f → ∀ {a : ℝ}, 0<a → ∀ m : ℕ,
    (∫ x,‖gradient (band f a (2*((2:ℝ)^m*a))) x‖) ≤ C*(∫ x,‖gradient f x‖) := by
  obtain ⟨C,hC,he⟩ := smooth_compact_dyadic_band
  refine ⟨C,hC,?_⟩
  intro f hf hc a ha m
  simpa only [geometric_band_eq] using he hf hc ha m

end SobolevBand

namespace WeakSobolev
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

lemma HasGradient.comp_isometry {f : F → ℝ} {g : F → F}
    (hw : HasGradient (μ := volume) f g) (e : E ≃ₗᵢ[ℝ] F) :
    HasGradient (μ := volume) (fun x => f (e x)) (fun x => e.symm (g (e x))) := by
  intro φ hφ hc v
  let ψ := φ ∘ e.symm
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp e.symm.contDiff
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph e.symm.toHomeomorph
  have hd x : fderiv ℝ ψ (e x) (e v)=fderiv ℝ φ x v := by
    rw [fderiv_comp (e x) (hφ.differentiable (by simp) _) (e.symm.differentiableAt),e.symm.fderiv]
    change fderiv ℝ φ (e.symm (e x)) (e.symm (e v))=fderiv ℝ φ x v
    simp only [e.symm_apply_apply]
  have hi x : ⟪e.symm (g (e x)),v⟫=⟪g (e x),e v⟫ := by
    simpa only [e.apply_symm_apply] using (e.inner_map_map (e.symm (g (e x))) v).symm
  have h := hw ψ hψ hψc (e v)
  rw [← e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding (fun y => f y*fderiv ℝ ψ y (e v)),
    ← e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding (fun y => ⟪g y,e v⟫*ψ y)] at h
  simpa only [hd,← hi,ψ,Function.comp_apply,e.symm_apply_apply] using h
end WeakSobolev

namespace CenteredDiskEndpoint
open WeakSobolev

lemma hasGradient_iff_hasWeakGradient {f : Plane → ℝ} {g : Plane → Plane}
    (hf : LocallyIntegrable f) (hg : Integrable g) :
    HasGradient (μ := volume) f g ↔ HasWeakGradient f g := by
  constructor
  · intro hw φ hφ hc i
    simpa only [testPartial,EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul]
      using hw φ hφ hc (EuclideanSpace.single i 1)
  · intro hw φ hφ hc v
    have hv : v=∑ i : Fin 2,v i • EuclideanSpace.single i 1 := by
      simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
        ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v).symm
    have hleft i : Integrable (fun x => f x*testPartial φ i x) :=
      hf.integrable_smul_right_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ _)
    have hright i : Integrable (fun x => g x i*φ x) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hg).locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
    have hd x : f x*fderiv ℝ φ x v=∑ i : Fin 2,v i*(f x*testPartial φ i x) := by
      conv_lhs => rw [hv]
      simp only [_root_.map_sum,map_smul,smul_eq_mul,Finset.mul_sum,testPartial]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hi x : ⟪g x,v⟫*φ x=∑ i : Fin 2,v i*(g x i*φ x) := by
      conv_lhs => rw [hv]
      simp only [inner_sum,real_inner_smul_right,EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hd,hi]
    rw [integral_finsetSum _ (fun i _ => (hleft i).const_mul _),
      integral_finsetSum _ (fun i _ => (hright i).const_mul _)]
    simp only [integral_const_mul,hw φ hφ hc,Finset.sum_neg_distrib,mul_neg]

/-- The coordinate isometry preserves Euclidean, not max-product, norms. -/
def complexPlane : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

lemma integrable_comp_complexPlane {F : Type*} [NormedAddCommGroup F] {f : Plane → F} :
    Integrable (fun z => f (complexPlane z)) ↔ Integrable f :=
  complexPlane.measurePreserving.integrable_comp_emb complexPlane.toMeasurableEquiv.measurableEmbedding

lemma integrable_comp_complexPlane_symm {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} :
    Integrable (fun x => f (complexPlane.symm x)) ↔ Integrable f :=
  complexPlane.symm.measurePreserving.integrable_comp_emb complexPlane.symm.toMeasurableEquiv.measurableEmbedding

lemma locallyIntegrable_comp_complexPlane {f : Plane → ℝ} :
    LocallyIntegrable (fun z => f (complexPlane z)) ↔ LocallyIntegrable f := by
  have h := locallyIntegrable_map_homeomorph complexPlane.toHomeomorph (f := f) (μ := volume)
  change LocallyIntegrable f (Measure.map complexPlane volume) ↔ LocallyIntegrable (fun z => f (complexPlane z)) at h
  rw [complexPlane.measurePreserving.map_eq] at h
  exact h.symm

lemma gradientNorm_comp_complexPlane (g : Plane → Plane) :
    (∫ z,‖complexPlane.symm (g (complexPlane z))‖)=gradientNorm g := by
  simp only [LinearIsometryEquiv.norm_map,gradientNorm]
  exact complexPlane.measurePreserving.integral_comp complexPlane.toMeasurableEquiv.measurableEmbedding (fun x => ‖g x‖)

lemma gradientNorm_comp_complexPlane_symm (G : ℂ → ℂ) :
    gradientNorm (fun x => complexPlane (G (complexPlane.symm x)))=∫ z,‖G z‖ := by
  simp only [LinearIsometryEquiv.norm_map,gradientNorm]
  exact complexPlane.symm.measurePreserving.integral_comp complexPlane.symm.toMeasurableEquiv.measurableEmbedding (fun z => ‖G z‖)
end CenteredDiskEndpoint

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff Convolution

namespace SobolevBand
open DiskMoments RadiusEnvelope ContinuousLinearMap

lemma band_self (f : ℂ → ℝ) (a : ℝ) :
    band f a a = fun x => signedAverage f x a := by
  funext x
  simp [band, envelope, Set.Icc_self]

/-- The normalized open-disk kernel, without an absolute value on the input. -/
def diskKernel (a : ℝ) : ℂ → ℝ :=
  (Metric.ball (0 : ℂ) a).indicator (fun _ => (Real.pi * a^2)⁻¹)

lemma diskKernel_nonneg (a : ℝ) (x : ℂ) : 0 ≤ diskKernel a x := by
  apply Set.indicator_nonneg
  intro y hy
  positivity

lemma diskKernel_integrable (a : ℝ) : Integrable (diskKernel a) := by
  exact (integrableOn_const measure_ball_lt_top.ne).integrable_indicator measurableSet_ball

lemma diskKernel_integral_abs {a : ℝ} (ha : 0 < a) :
    (∫ x, |diskKernel a x|) = 1 := by
  simp_rw [abs_of_nonneg (diskKernel_nonneg a _)]
  rw [diskKernel, integral_indicator measurableSet_ball, setIntegral_const,
    measureReal_def, Complex.volume_ball]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal ha.le,
    smul_eq_mul]
  change a^2 * Real.pi * (Real.pi*a^2)⁻¹ = 1
  field_simp

lemma diskKernel_convolution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : ℂ → F) (a : ℝ) (x : ℂ) :
    (diskKernel a ⋆[lsmul ℝ ℝ, volume] g) x =
      (Real.pi*a^2)⁻¹ • ∫ y in Metric.ball x a, g y := by
  rw [convolution_eq_swap, ← integral_smul, ← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  have hm : x-y ∈ Metric.ball (0 : ℂ) a ↔ y ∈ Metric.ball x a := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]
  by_cases hy : y ∈ Metric.ball x a
  · simp only [diskKernel, Set.indicator_of_mem (hm.mpr hy), Set.indicator_of_mem hy,
      lsmul_apply]
  · simp only [diskKernel, Set.indicator_of_notMem (mt hm.mp hy),
      Set.indicator_of_notMem hy, lsmul_apply, zero_smul]

lemma smooth_band_self_bound {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) {a : ℝ} (ha : 0 < a) :
    (∫ x, ‖gradient (band f a a) x‖) ≤ ∫ x, ‖gradient f x‖ := by
  have hgi : Integrable (gradient f) :=
    (continuous_gradient hf).integrable_of_hasCompactSupport (gradient_hasCompactSupport hc)
  obtain ⟨L, hL⟩ := hf.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  have he : gradient (band f a a) = diskKernel a ⋆[lsmul ℝ ℝ, volume] gradient f := by
    funext x
    rw [band_self, gradient_signedAverage hf
      (fun y => norm_fderiv_le_of_lipschitz ℝ hL (x₀ := y)) x ha,
      diskKernel_convolution]
  rw [he]
  have h := WeakSobolev.norm_convolution_le (diskKernel_integrable a) hgi
  simpa only [diskKernel_integral_abs ha, one_mul] using h

/-- The natural index includes zero, with one absolute constant for both cases. -/
theorem smooth_dyadic_bound_including_zero : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {f : ℂ → ℝ}, ContDiff ℝ 1 f → HasCompactSupport f →
    ∀ {a : ℝ}, 0 < a → ∀ m : ℕ,
      (∫ x, ‖gradient (band f a ((2 : ℝ)^m*a)) x‖) ≤ C*(∫ x, ‖gradient f x‖) := by
  obtain ⟨C, hC, hbound⟩ := smooth_dyadic_bound
  refine ⟨max C 1, (le_max_right C 1).trans' zero_le_one, ?_⟩
  intro f hf hc a ha m
  have hv : 0 ≤ ∫ x, ‖gradient f x‖ := integral_nonneg (fun x => norm_nonneg _)
  cases m with
  | zero =>
      simpa only [pow_zero, one_mul] using
        (smooth_band_self_bound hf hc ha).trans
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_right C 1) hv)
  | succ n =>
      have he : (2 : ℝ)^(n+1)*a = 2*((2 : ℝ)^n*a) := by rw [pow_succ]; ring
      rw [he]
      exact (hbound hf hc ha n).trans
        (mul_le_mul_of_nonneg_right (le_max_left C 1) hv)

end SobolevBand

namespace CenteredDiskEndpoint
open DiskMoments SobolevBand WeakSobolev

theorem plane_finiteDimensional : FiniteDimensional ℝ Plane := inferInstance

theorem plane_borelSpace : BorelSpace Plane := inferInstance

theorem plane_completeSpace : CompleteSpace Plane := inferInstance

lemma signedAverage_comp_complexPlane (f : Plane → ℝ) (z : ℂ) (r : ℝ) :
    signedAverage (fun w => f (complexPlane w)) z r = diskAverage f (complexPlane z) r := by
  unfold signedAverage diskAverage
  congr 1
  have h := complexPlane.measurePreserving.setIntegral_image_emb
    complexPlane.toMeasurableEquiv.measurableEmbedding f (Metric.ball z r)
  rw [complexPlane.image_ball] at h
  exact h.symm

lemma signedBand_comp_complexPlane (f : Plane → ℝ) (a b : ℝ) :
    band (fun w => f (complexPlane w)) a b = fun z => signedBand f a b (complexPlane z) := by
  funext z
  simp only [band, RadiusEnvelope.envelope, signedBand, signedAverage_comp_complexPlane]

lemma gradient_comp_complexPlane {f : Plane → ℝ} (hf : Differentiable ℝ f) (z : ℂ) :
    gradient (fun w => f (complexPlane w)) z = complexPlane.symm (gradient f (complexPlane z)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  change fderiv ℝ (f ∘ complexPlane) z v = _
  rw [fderiv_comp z (hf _) complexPlane.differentiableAt, complexPlane.fderiv]
  change fderiv ℝ f (complexPlane z) (complexPlane v) = _
  rw [← inner_gradient_left]
  simpa only [complexPlane.apply_symm_apply] using
    complexPlane.inner_map_map (complexPlane.symm (gradient f (complexPlane z))) v

theorem main_signed_finite_band : SignedFiniteBandStatement := by
  obtain ⟨C, hC, hbound⟩ := smooth_dyadic_bound_including_zero
  refine ⟨C, hC, ?_⟩
  intro f hf hc a ha m
  let f' : ℂ → ℝ := fun z => f (complexPlane z)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hf' : ContDiff ℝ 1 f' := hf1.comp complexPlane.contDiff
  have hc' : HasCompactSupport f' := hc.comp_homeomorph complexPlane.toHomeomorph
  have hab : a ≤ (2 : ℝ)^m*a := by
    have hp : (1 : ℝ) ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp ha.le
  have hL := smooth_band_lipschitz hf' hc' ha hab
  have hFi' := hL.continuous.locallyIntegrable (μ := volume)
  have hGi' := smooth_band_integrable_gradient hf' hc' ha hab
  have he : band f' a ((2 : ℝ)^m*a) =
      fun z => signedBand f a ((2 : ℝ)^m*a) (complexPlane z) :=
    signedBand_comp_complexPlane f a _
  have hFi : LocallyIntegrable (signedBand f a ((2 : ℝ)^m*a)) := by
    apply locallyIntegrable_comp_complexPlane.mp
    simpa only [he] using hFi'
  let G' := gradient (band f' a ((2 : ℝ)^m*a))
  let G := fun x => complexPlane (G' (complexPlane.symm x))
  have hG0 : Integrable (fun x => G' (complexPlane.symm x)) :=
    integrable_comp_complexPlane_symm.mpr hGi'
  have hGi : Integrable G :=
    complexPlane.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hG0
  have hw' : HasGradient (μ := volume) (band f' a ((2 : ℝ)^m*a)) G' :=
    lipschitz_hasGradient hL
  have hw0 := hw'.comp_isometry complexPlane.symm
  have hw : HasWeakGradient (signedBand f a ((2 : ℝ)^m*a)) G := by
    apply (hasGradient_iff_hasWeakGradient hFi hGi).mp
    simpa only [he, complexPlane.apply_symm_apply, LinearIsometryEquiv.symm_symm] using hw0
  refine ⟨hFi, G, hGi, hw, ?_⟩
  have hnorm : (∫ z, ‖gradient f' z‖) = gradientNorm (gradient f) := by
    calc
      _ = ∫ z, ‖complexPlane.symm (gradient f (complexPlane z))‖ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => congrArg norm
          (gradient_comp_complexPlane (hf1.differentiable one_ne_zero) z))
      _ = _ := gradientNorm_comp_complexPlane (gradient f)
  rw [show gradientNorm G = ∫ z, ‖G' z‖ from gradientNorm_comp_complexPlane_symm G']
  exact (hbound hf' hc' ha m).trans_eq (congrArg (fun v => C*v) hnorm)

end CenteredDiskEndpoint

end SignedDisk

end

end OAI
