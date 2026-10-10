import OAI.Analysis.DiskMaximal.Geometry

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff

noncomputable section

namespace DiskMoments

local instance : Fact (Module.finrank ℝ ℂ = 2) := ⟨Complex.finrank_real_complex⟩

def rotation (t : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ := Complex.orientation.rotation (t : Real.Angle)

lemma rotation_apply (t : ℝ) (z : ℂ) :
    rotation t z = ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) * z := by
  simp only [rotation, Complex.rotation, Real.Angle.coe_toCircle, Real.Angle.cos_coe, Real.Angle.sin_coe]

lemma rotation_zero (z : ℂ) : rotation 0 z = z := by simp [rotation_apply]

lemma rotation_norm (t : ℝ) (z : ℂ) : ‖rotation t z‖ = ‖z‖ :=
  (rotation t).norm_map z

lemma integral_rotation (g : ℂ → ℝ) (x : ℂ) (r t : ℝ) :
    (∫ z in Metric.ball 0 r, g (x + rotation t z)) =
      ∫ z in Metric.ball 0 r, g (x + z) := by
  have hpre : (rotation t) ⁻¹' Metric.ball (0 : ℂ) r = Metric.ball 0 r := by
    ext z
    simp [Metric.mem_ball, dist_zero_right]
  have h := (rotation t).measurePreserving.setIntegral_preimage_emb
    (rotation t).toHomeomorph.measurableEmbedding (fun z => g (x + z)) (Metric.ball 0 r)
  rw [hpre] at h
  exact h

lemma hasDerivAt_rotation (t : ℝ) (z : ℂ) :
    HasDerivAt (fun a : ℝ => rotation a z) (Complex.I * rotation t z) t := by
  simp only [rotation_apply]
  convert! (((Real.hasDerivAt_cos t).ofReal_comp.add
    ((Real.hasDerivAt_sin t).ofReal_comp.mul_const Complex.I )).mul_const z) using 1; try rfl
  simp only [Complex.ofReal_neg]
  ring_nf
  simp [sub_eq_add_neg]

/-- The circulation moment of a smooth gradient on a disk vanishes. -/
theorem rotational_moment_zero {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) (r : ℝ) :
    (∫ z in Metric.ball 0 r, (fderiv ℝ g (x + z)) (Complex.I * z)) = 0 := by
  let F : ℝ → ℂ → ℝ := fun t z => g (x + rotation t z)
  let F' : ℝ → ℂ → ℝ := fun t z =>
    (fderiv ℝ g (x + rotation t z)) (Complex.I * rotation t z)
  have hdc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hdc.continuousOn
  have hFm (t : ℝ) : Continuous (F t) := hg.continuous.comp (by fun_prop)
  have hF'm (t : ℝ) : Continuous (F' t) := by
    unfold F'
    exact (hdc.comp (by fun_prop)).clm_apply (by fun_prop)
  have hFi : IntegrableOn (F 0) (Metric.ball 0 r) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 r) (hFm 0).continuousOn).mono_set
      Metric.ball_subset_closedBall
  have hdiff (z : ℂ) (t : ℝ) : HasDerivAt (fun t => F t z) (F' t z) t := by
    exact ((hg.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_rotation t z).const_add x))
  have hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) r), ∀ t ∈ (univ : Set ℝ),
      ‖F' t z‖ ≤ max C 0 * r := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz t _
    have hz' : ‖z‖ ≤ r := by simpa [Metric.mem_ball, dist_zero_right] using (show ‖z‖ < r by simpa [Metric.mem_ball, dist_zero_right] using hz).le
    have hpos : x + rotation t z ∈ Metric.closedBall x r := by
      simpa [Metric.mem_closedBall, dist_eq_norm, rotation_norm] using hz'
    exact ((fderiv ℝ g (x + rotation t z)).le_opNorm _).trans
      (mul_le_mul ((hC _ hpos).trans (le_max_left _ _))
        (by simpa [norm_mul, rotation_norm] using hz') (norm_nonneg _) (le_max_right _ _))
  have hb : IntegrableOn (fun _ : ℂ => max C 0 * r) (Metric.ball 0 r) := by
    exact integrableOn_const (by finiteness)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Metric.ball (0 : ℂ) r))
    (x₀ := (0 : ℝ)) (s := univ) (F := F) (F' := F') (bound := fun _ => max C 0 * r)
    Filter.univ_mem (Filter.Eventually.of_forall (fun t => (hFm t).aestronglyMeasurable))
    hFi (hF'm 0).aestronglyMeasurable hbound hb
    (Filter.Eventually.of_forall (fun z t _ => hdiff z t))).2
  have hconst : (fun t => ∫ z in Metric.ball 0 r, F t z) =
      fun _ => ∫ z in Metric.ball 0 r, g (x + z) := by
    funext t
    exact integral_rotation g x r t
  rw [hconst] at hd
  have he := hd.unique (hasDerivAt_const 0 (∫ z in Metric.ball 0 r, g (x + z)))
  simpa only [F', rotation_zero] using he

lemma integral_translate_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (x : ℂ) (r : ℝ) :
    (∫ z in Metric.ball 0 r, f (x + z)) = ∫ y in Metric.ball x r, f y := by
  have hpre : (fun z : ℂ => x + z) ⁻¹' Metric.ball x r = Metric.ball 0 r := by
    ext z
    simp [Metric.mem_ball, dist_eq_norm]
  have h := (measurePreserving_add_left volume x).setIntegral_preimage_emb
    (Homeomorph.addLeft x).measurableEmbedding f (Metric.ball x r)
  rwa [hpre] at h

lemma continuous_gradient {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (gradient g) :=
  (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp (hg.continuous_fderiv one_ne_zero)

lemma real_moment_integrand (g : ℂ → ℝ) (x z : ℂ) :
    (star z * gradient g x).re = (fderiv ℝ g x) z := by
  rw [← inner_gradient_left, Complex.inner]
  simp [mul_comm]

lemma imaginary_moment_integrand (g : ℂ → ℝ) (x z : ℂ) :
    (star z * gradient g x).im = (fderiv ℝ g x) (Complex.I * z) := by
  rw [← inner_gradient_left, Complex.inner]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The imaginary part of the actual complex disk moment is zero. -/
theorem imaginary_moment_zero {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) (r : ℝ) :
    (∫ y in Metric.ball x r, star (y - x) * gradient g y).im = 0 := by
  have ht := (integral_translate_ball (fun y => star (y-x) * gradient g y) x r).symm
  rw [ht]
  have hi : IntegrableOn (fun z => star ((x+z)-x) * gradient g (x+z)) (Metric.ball 0 r) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 r)
      ((by fun_prop : Continuous (fun z : ℂ => star ((x+z)-x))).mul
        ((continuous_gradient hg).comp (by fun_prop))).continuousOn).mono_set
      Metric.ball_subset_closedBall
  change Complex.imCLM (∫ z in Metric.ball 0 r, star ((x+z)-x) * gradient g (x+z)) = 0
  rw [← Complex.imCLM.integral_comp_comm hi]
  convert rotational_moment_zero hg x r using 1
  congr 1
  funext z
  simpa using imaginary_moment_integrand g (x+z) z

/-- Differentiate a disk average on its fixed unit-disk model. -/
theorem hasDerivAt_integral_unitDisk {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1, g (x + s • z))
      (∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x + t • z)) z) t := by
  let F : ℝ → ℂ → ℝ := fun s z => g (x + s • z)
  let F' : ℝ → ℂ → ℝ := fun s z => (fderiv ℝ g (x + s • z)) z
  have hdc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (isCompact_closedBall x (|t|+1)).exists_bound_of_continuousOn hdc.continuousOn
  have hFm (s : ℝ) : Continuous (F s) := hg.continuous.comp (by fun_prop)
  have hF'm (s : ℝ) : Continuous (F' s) := by
    unfold F'
    exact (hdc.comp (by fun_prop)).clm_apply continuous_id
  have hFi : IntegrableOn (F t) (Metric.ball 0 1) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1) (hFm t).continuousOn).mono_set
      Metric.ball_subset_closedBall
  have hdiff (z : ℂ) (s : ℝ) : HasDerivAt (fun s => F s z) (F' s z) s := by
    convert! ((hg.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt s
        (((hasDerivAt_id s).smul_const z).const_add x)) using 1
    simp [F', id_eq]
  have hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      ∀ s ∈ Metric.ball t 1, ‖F' s z‖ ≤ max C 0 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz s hs
    have hz' : ‖z‖ ≤ 1 := by simpa [Metric.mem_ball, dist_zero_right] using
      (show ‖z‖ < 1 by simpa [Metric.mem_ball, dist_zero_right] using hz).le
    have hs' : |s| ≤ |t| + 1 := by
      have hh : |s-t| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hs
      have hh' := abs_add_le (s-t) t
      rw [sub_add_cancel] at hh'
      linarith
    have hpos : x + s • z ∈ Metric.closedBall x (|t|+1) := by
      simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hz' (abs_nonneg s)).trans (by simpa using hs')
    exact ((fderiv ℝ g (x+s•z)).le_opNorm _).trans
      (by simpa only [mul_one] using (mul_le_mul ((hC _ hpos).trans (le_max_left C 0)) hz'
        (norm_nonneg _) (le_max_right C 0)))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Metric.ball (0 : ℂ) 1))
    (x₀ := t) (s := Metric.ball t 1) (F := F) (F' := F') (bound := fun _ => max C 0)
    (Metric.ball_mem_nhds _ zero_lt_one) (Filter.Eventually.of_forall (fun s => (hFm s).aestronglyMeasurable))
    hFi (hF'm t).aestronglyMeasurable hbound (integrableOn_const (by finiteness))
    (Filter.Eventually.of_forall (fun z s _ => hdiff z s))).2

lemma integral_scale_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) {t : ℝ} (ht : 0 < t) :
    (∫ z in Metric.ball (0 : ℂ) 1, f (t • z)) =
      (t^2)⁻¹ • ∫ z in Metric.ball (0 : ℂ) t, f z := by
  convert Measure.setIntegral_comp_smul_of_pos volume f (Metric.ball 0 1) ht using 1
  rw [Complex.finrank_real_complex, smul_ball ht.ne', smul_zero, Real.norm_eq_abs, abs_of_pos ht, mul_one]

/-- Signed normalized average on a centered Euclidean disk in the complex plane. -/
def signedAverage (g : ℂ → ℝ) (x : ℂ) (t : ℝ) : ℝ :=
  (∫ y in Metric.ball x t, g y) / (Real.pi * t^2)

lemma signedAverage_fixedDomain (g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    signedAverage g x t = (∫ z in Metric.ball (0 : ℂ) 1, g (x + t • z)) / Real.pi := by
  rw [integral_scale_ball (fun z => g (x+z)) ht, integral_translate_ball]
  simp only [signedAverage, smul_eq_mul]
  ring

lemma integral_fderiv_scale (g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x+t•z)) z) =
      (t^3)⁻¹ * ∫ y in Metric.ball x t, (fderiv ℝ g y) (y-x) := by
  have hi (z : ℂ) : (fderiv ℝ g (x+t•z)) z =
      t⁻¹ * (fderiv ℝ g (x+t•z)) (t•z) := by
    rw [map_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
  simp_rw [hi]
  rw [integral_const_mul, integral_scale_ball (fun z => (fderiv ℝ g (x+z)) z) ht]
  have hh : (∫ z in Metric.ball (0 : ℂ) t, (fderiv ℝ g (x+z)) z) =
      ∫ y in Metric.ball x t, (fderiv ℝ g y) (y-x) := by
    simpa using integral_translate_ball (fun y => (fderiv ℝ g y) (y-x)) x t
  rw [hh]
  simp only [smul_eq_mul]
  ring

lemma integral_fderiv_moment_real {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ) (t : ℝ) :
    (∫ y in Metric.ball x t, (fderiv ℝ g y) (y-x)) =
      (∫ y in Metric.ball x t, star (y-x) * gradient g y).re := by
  have hi : IntegrableOn (fun y => star (y-x) * gradient g y) (Metric.ball x t) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall x t)
      ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul
        (continuous_gradient hg)).continuousOn).mono_set Metric.ball_subset_closedBall
  change _ = Complex.reCLM _
  rw [← Complex.reCLM.integral_comp_comm hi]
  congr 1
  funext y
  exact (real_moment_integrand g y (y-x)).symm

/-- The radial disk derivative is the real part of its complex moment. -/
theorem hasDerivAt_signedAverage {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (signedAverage g x)
      ((∫ y in Metric.ball x t, star (y-x) * gradient g y).re / (Real.pi * t^3)) t := by
  have hd := (hasDerivAt_integral_unitDisk hg x t).div_const Real.pi
  rw [integral_fderiv_scale g x ht, integral_fderiv_moment_real hg x t] at hd
  have he : (fun s => (∫ z in Metric.ball (0 : ℂ) 1, g (x+s•z)) / Real.pi)
      =ᶠ[𝓝 t] signedAverage g x := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (signedAverage_fixedDomain g x hs).symm
  convert! hd.congr_of_eventuallyEq he.symm using 1; try rfl
  ring

lemma ball_ae_closedBall (x : ℂ) (r : ℝ) :
    Metric.ball x r =ᵐ[volume] Metric.closedBall x r := by
  apply ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
  · exact (Measure.addHaar_closedBall_eq_addHaar_ball volume x r).le
  · exact measurableSet_ball.nullMeasurableSet
  · exact measure_closedBall_lt_top.ne

lemma continuous_integral_fderiv_unit {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ) :
    Continuous (fun t : ℝ => ∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x+t•z)) z) := by
  have he (t : ℝ) : (∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x+t•z)) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1, (fderiv ℝ g (x+t•z)) z :=
    setIntegral_congr_set (ball_ae_closedBall 0 1)
  simp_rw [he]
  apply continuous_parametric_integral_of_continuous _ (isCompact_closedBall 0 1)
  exact ((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply continuous_snd

end DiskMoments

open MeasureTheory Set Filter
open scoped Topology Interval NNReal

noncomputable section
namespace DiskKernels

/-- An ordinary nonnegative probability density supported on a radius interval. -/
structure RadiusDensity (a b : ℝ) (M : ℝ≥0) where
  toFun : ℝ → ℝ
  integrable : Integrable toFun
  nonneg : ∀ t, 0 ≤ toFun t
  integral_one : ∫ t, toFun t = 1
  bound : ∀ t, toFun t ≤ M
  support : ∀ t, t ∉ Icc a b → toFun t = 0

instance {a b : ℝ} {M : ℝ≥0} : CoeFun (RadiusDensity a b M) (fun _ => ℝ → ℝ) :=
  ⟨RadiusDensity.toFun⟩

def tail {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (u : ℝ) : ℝ :=
  ∫ t in Ioi u, k t

lemma tail_nonneg {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (u : ℝ) :
    0 ≤ tail k u := integral_nonneg k.nonneg

lemma tail_le_one {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (u : ℝ) :
    tail k u ≤ 1 := by
  rw [← k.integral_one]
  exact setIntegral_le_integral k.integrable (Eventually.of_forall k.nonneg)

lemma tail_one {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) {u : ℝ} (hu : u < a) :
    tail k u = 1 := by
  rw [tail, setIntegral_eq_integral_of_forall_compl_eq_zero, k.integral_one]
  intro t ht
  apply k.support
  simp only [mem_Ioi, not_lt] at ht
  intro h
  linarith [h.1]

lemma tail_zero {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) {u : ℝ} (hu : b ≤ u) :
    tail k u = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply k.support
  intro h
  have := ht
  simp only [mem_Ioi] at this
  linarith [h.2]

lemma tail_lipschitz {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) :
    LipschitzWith M (tail k) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [Real.dist_eq, ← Real.norm_eq_abs, tail, tail,
    intervalIntegral.integral_Ioi_sub_Ioi' k.integrable.integrableOn k.integrable.integrableOn]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (f := k) (C := (M : ℝ)) (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (k.nonneg t)]
      exact k.bound t)
  simpa only [Real.dist_eq, abs_sub_comm v u] using h

def kernel {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x y : ℂ) : ℝ :=
  tail k (dist y x)

lemma kernel_lipschitz {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x : ℂ) :
    LipschitzWith M (kernel k x) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  exact ((tail_lipschitz k).dist_le_mul (dist y x) (dist z x)).trans
    (mul_le_mul_of_nonneg_left (dist_dist_dist_le_left y z x) M.coe_nonneg)

lemma kernel_one {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x : ℂ)
    {y : ℂ} (hy : y ∈ Metric.ball x a) : kernel k x y = 1 := tail_one k hy

lemma kernel_zero {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x : ℂ)
    {y : ℂ} (hy : y ∉ Metric.ball x b) : kernel k x y = 0 :=
  tail_zero k (not_lt.mp hy)

/-- The radial tail is exactly the positive average of disk indicators. -/
lemma kernel_eq_integral {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x y : ℂ) :
    kernel k x y = ∫ t, k t * (Metric.ball x t).indicator (fun _ => (1 : ℝ)) y := by
  rw [kernel, tail, ← integral_indicator measurableSet_Ioi]
  congr 1
  funext t
  by_cases ht : dist y x < t
  · simp [Set.indicator_of_mem, ht, Metric.mem_ball]
  · simp [Set.indicator_of_notMem, ht, Metric.mem_ball]

/-- Convex combinations preserve all density and support bounds. -/
def mix {a b : ℝ} {M : ℝ≥0} (k l : RadiusDensity a b M)
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : RadiusDensity a b M where
  toFun t := w * k t + (1-w) * l t
  integrable := (k.integrable.const_mul w).add (l.integrable.const_mul (1-w))
  nonneg t := add_nonneg (mul_nonneg hw0 (k.nonneg t)) (mul_nonneg (sub_nonneg.mpr hw1) (l.nonneg t))
  integral_one := by
    rw [integral_add (k.integrable.const_mul w) (l.integrable.const_mul (1-w)),
      integral_const_mul, integral_const_mul, k.integral_one, l.integral_one]
    ring
  bound t := by
    have h₁ := mul_le_mul_of_nonneg_left (k.bound t) hw0
    have h₂ := mul_le_mul_of_nonneg_left (l.bound t) (sub_nonneg.mpr hw1)
    nlinarith
  support t ht := by rw [k.support t ht, l.support t ht]; ring

/-- Two oppositely signed moments admit an explicit convex zero. -/
lemma convex_zero {A B : ℝ} (hA : 0 ≤ A) (hB : B ≤ 0) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ w*A+(1-w)*B = 0 := by
  by_cases h : A-B=0
  · refine ⟨1, zero_le_one, le_rfl, ?_⟩
    have : A = 0 := by linarith
    simp [this]
  · have hp : 0 < A-B := lt_of_le_of_ne (by linarith) (Ne.symm h)
    refine ⟨-B/(A-B), div_nonneg (neg_nonneg.mpr hB) hp.le, ?_, ?_⟩
    · apply (div_le_one hp).mpr
      linarith
    · field_simp
      ring

def inverseCube (t : ℝ) : ℝ := (t^3)⁻¹

def cubeMass (a b : ℝ) : ℝ := ∫ t in Icc a b, inverseCube t

lemma inverseCube_bounds {t : ℝ} (ht : t ∈ Icc ((1 : ℝ)/2) 3) :
    (1 : ℝ)/27 ≤ inverseCube t ∧ inverseCube t ≤ 8 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hl : (1 : ℝ)/8 ≤ t^3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) ht.1 3
    norm_num at this
    exact this
  have hu : t^3 ≤ 27 := by
    have := pow_le_pow_left₀ ht0.le ht.2 3
    norm_num at this
    exact this
  constructor
  · simpa [inverseCube, one_div] using one_div_le_one_div_of_le (pow_pos ht0 3) hu
  · simpa [inverseCube, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/8) hl

lemma continuousOn_inverseCube {a b : ℝ} (ha : 0 < a) :
    ContinuousOn inverseCube (Icc a b) := by
  apply (continuous_id.pow 3).continuousOn.inv₀
  intro t ht
  exact pow_ne_zero 3 (ne_of_gt (lt_of_lt_of_le ha ht.1))

lemma cubeMass_lower {a b : ℝ} (ha : (1 : ℝ)/2 ≤ a) (hb : b ≤ 3) :
    (b-a)/27 ≤ cubeMass a b := by
  by_cases hab : a ≤ b
  · have hi := (continuousOn_inverseCube (b := b) (show 0 < a by linarith)).integrableOn_Icc (μ := volume)
    have h := setIntegral_mono_on (f := fun _ : ℝ => (1 : ℝ)/27)
      (integrableOn_const isCompact_Icc.measure_ne_top) hi measurableSet_Icc
      (fun t ht => (inverseCube_bounds ⟨ha.trans ht.1, ht.2.trans hb⟩).1)
    simp only [setIntegral_const, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul] at h
    simpa only [cubeMass, div_eq_mul_inv, one_mul] using h
  · have he : Icc a b = ∅ := Icc_eq_empty hab
    have hx : cubeMass a b = 0 := by simp [cubeMass, he]
    rw [hx]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hab)) (by norm_num)

lemma cubeMass_pos {a b : ℝ} (ha : (1 : ℝ)/2 ≤ a) (hb : b ≤ 3) (hab : a < b) :
    0 < cubeMass a b := (div_pos (sub_pos.mpr hab) (by norm_num)).trans_le (cubeMass_lower ha hb)

def cubeDensity (a b t : ℝ) : ℝ :=
  (Icc a b).indicator (fun t => inverseCube t / cubeMass a b) t

lemma cubeDensity_integrable {a b : ℝ} (ha : 0 < a) : Integrable (cubeDensity a b) :=
  ((continuousOn_inverseCube ha).div_const (cubeMass a b)).integrableOn_Icc.integrable_indicator
    measurableSet_Icc

lemma cubeDensity_integral {a b : ℝ} (ha : (1 : ℝ)/2 ≤ a) (hb : b ≤ 3) (hab : a < b) :
    (∫ t, cubeDensity a b t) = 1 := by
  simp only [cubeDensity]
  rw [integral_indicator measurableSet_Icc, integral_div, ← cubeMass,
    div_self (cubeMass_pos ha hb hab).ne']

lemma cubeDensity_nonneg {a b : ℝ} (ha : (1 : ℝ)/2 ≤ a) (hb : b ≤ 3) (hab : a < b)
    (t : ℝ) : 0 ≤ cubeDensity a b t := by
  apply Set.indicator_nonneg
  intro t ht
  exact div_nonneg ((by norm_num : (0 : ℝ) ≤ 1/27).trans
    (inverseCube_bounds ⟨ha.trans ht.1, ht.2.trans hb⟩).1) (cubeMass_pos ha hb hab).le

lemma cubeDensity_bound {a b : ℝ} (ha : (1 : ℝ)/2 ≤ a) (hb : b ≤ 3) (hab : a < b)
    (t : ℝ) : cubeDensity a b t ≤ 216/(b-a) := by
  by_cases ht : t ∈ Icc a b
  · rw [cubeDensity, Set.indicator_of_mem ht]
    have hM := cubeMass_pos ha hb hab
    have hl := cubeMass_lower ha hb
    have hbnd := (inverseCube_bounds ⟨ha.trans ht.1, ht.2.trans hb⟩).2
    apply (div_le_iff₀ hM).mpr
    have hD : 0 < b-a := sub_pos.mpr hab
    have hl' : 8 ≤ 216/(b-a) * cubeMass a b := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).mpr
      linarith
    exact hbnd.trans hl'
  · simp only [cubeDensity, Set.indicator_of_notMem ht]
    positivity

/-- The concrete normalized inverse-cube density, with an absolute width bound. -/
def inverseCubeDensity (a b : ℝ) (ha : (1 : ℝ)/2 ≤ a) (hb : b ≤ 3) (hab : a < b) :
    RadiusDensity a b ⟨216/(b-a), by positivity⟩ where
  toFun := cubeDensity a b
  integrable := cubeDensity_integrable (by linarith)
  nonneg := cubeDensity_nonneg ha hb hab
  integral_one := cubeDensity_integral ha hb hab
  bound := cubeDensity_bound ha hb hab
  support t ht := Set.indicator_of_notMem ht _

def enlarge {a b a' b' : ℝ} {M N : ℝ≥0} (k : RadiusDensity a b M)
    (ha : a' ≤ a) (hb : b ≤ b') (hM : M ≤ N) : RadiusDensity a' b' N where
  toFun := k
  integrable := k.integrable
  nonneg := k.nonneg
  integral_one := k.integral_one
  bound t := (k.bound t).trans hM
  support t ht := k.support t (fun h => ht ⟨ha.trans h.1, h.2.trans hb⟩)

/-- Fubini identifies a radial kernel pairing with the average of disk pairings. -/
theorem kernel_pairing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x : ℂ)
    {f : ℂ → E} (hf : Integrable f) :
    (∫ y, kernel k x y • f y) = ∫ t, k t • ∫ y in Metric.ball x t, f y := by
  let A : Set (ℝ × ℂ) := {p | dist p.2 x < p.1}
  have hA : MeasurableSet A := measurableSet_lt (by fun_prop) measurable_fst
  let F : ℝ × ℂ → E := A.indicator (fun p => k p.1 • f p.2)
  have hF : Integrable F (volume.prod volume) := (k.integrable.smul_prod hf).indicator hA
  have hleft (t : ℝ) : (∫ y, F (t,y)) = k t • ∫ y in Metric.ball x t, f y := by
    have he : (fun y => F (t,y)) = fun y => k t • (Metric.ball x t).indicator f y := by
      funext y
      by_cases h : dist y x < t
      · simp [F, A, Metric.mem_ball, h]
      · simp [F, A, Metric.mem_ball, h]
    rw [he, integral_smul, integral_indicator measurableSet_ball]
  have hright (y : ℂ) : (∫ t, F (t,y)) = kernel k x y • f y := by
    have he : (fun t => F (t,y)) = fun t => (Ioi (dist y x)).indicator k t • f y := by
      funext t
      by_cases h : dist y x < t
      · simp [F, A, h]
      · simp [F, A, h]
    rw [he, integral_smul_const, integral_indicator measurableSet_Ioi]
    rfl
  have hh := integral_integral_swap (f := fun t y => F (t,y)) hF
  simp_rw [hleft, hright] at hh
  exact hh.symm

end DiskKernels

namespace DiskMoments
open DiskKernels

def moment (g : ℂ → ℝ) (x : ℂ) (t : ℝ) : ℂ :=
  ∫ y in Metric.ball x t, star (y-x) * gradient g y

def radialDerivative (g : ℂ → ℝ) (x : ℂ) (t : ℝ) : ℝ :=
  (∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x+t•z)) z) / Real.pi

lemma continuous_radialDerivative {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ) :
    Continuous (radialDerivative g x) := (continuous_integral_fderiv_unit hg x).div_const Real.pi

lemma moment_coefficient {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ)
    {t : ℝ} (ht : 0 < t) : (moment g x t).re / (Real.pi * t^3) = radialDerivative g x t := by
  rw [radialDerivative, integral_fderiv_scale g x ht, integral_fderiv_moment_real hg]
  simp only [moment]
  ring

lemma hasDerivAt_signedAverage_fixed {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (signedAverage g x) (radialDerivative g x t) t := by
  rw [← moment_coefficient hg x ht]
  exact hasDerivAt_signedAverage hg x ht

lemma moment_eq {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ)
    {t : ℝ} (ht : 0 < t) :
    moment g x t = ((Real.pi * t^3 * radialDerivative g x t : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    have hh := moment_coefficient hg x ht
    have hp : Real.pi * t^3 ≠ 0 := mul_ne_zero Real.pi_ne_zero (pow_ne_zero 3 ht.ne')
    exact (div_eq_iff hp).mp hh |>.trans (mul_comm _ _)
  · simpa only [moment, Complex.ofReal_im] using imaginary_moment_zero hg x t

lemma integral_radialDerivative {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in Icc a b, radialDerivative g x t) = signedAverage g x b - signedAverage g x a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ ((continuous_radialDerivative hg x).intervalIntegrable a b)
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact hasDerivAt_signedAverage_fixed hg x (lt_of_lt_of_le ha ht.1)

lemma cubeDensity_moment_integrable {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ)
    {a b : ℝ} (ha : 0 < a) :
    Integrable (fun t => cubeDensity a b t • moment g x t) := by
  have he : (fun t => cubeDensity a b t • moment g x t) =
      (Icc a b).indicator (fun t =>
        (((Real.pi / cubeMass a b) * radialDerivative g x t : ℝ) : ℂ)) := by
    funext t
    by_cases ht : t ∈ Icc a b
    · have ht0 := lt_of_lt_of_le ha ht.1
      rw [cubeDensity, Set.indicator_of_mem ht, Set.indicator_of_mem ht, moment_eq hg x ht0]
      apply Complex.ext <;> simp only [Complex.smul_re, Complex.smul_im, Complex.ofReal_re,
        Complex.ofReal_im, smul_eq_mul, mul_zero]
      simp only [inverseCube]
      field_simp
    · simp [cubeDensity, Set.indicator_of_notMem ht]
  rw [he]
  exact (Complex.continuous_ofReal.comp ((continuous_radialDerivative hg x).const_mul _)).continuousOn.integrableOn_Icc.integrable_indicator measurableSet_Icc

lemma cubeDensity_moment_integral {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t, cubeDensity a b t • moment g x t) =
      (((Real.pi / cubeMass a b) * (signedAverage g x b - signedAverage g x a) : ℝ) : ℂ) := by
  have he : (fun t => cubeDensity a b t • moment g x t) =
      (Icc a b).indicator (fun t =>
        (((Real.pi / cubeMass a b) * radialDerivative g x t : ℝ) : ℂ)) := by
    funext t
    by_cases ht : t ∈ Icc a b
    · have ht0 := lt_of_lt_of_le ha ht.1
      rw [cubeDensity, Set.indicator_of_mem ht, Set.indicator_of_mem ht, moment_eq hg x ht0]
      apply Complex.ext <;> simp only [Complex.smul_re, Complex.smul_im, Complex.ofReal_re,
        Complex.ofReal_im, smul_eq_mul, mul_zero]
      simp only [inverseCube]
      field_simp
    · simp [cubeDensity, Set.indicator_of_notMem ht]
  rw [he, integral_indicator measurableSet_Icc]
  change (∫ t in Icc a b, Complex.ofRealCLM ((Real.pi / cubeMass a b) * radialDerivative g x t)) = _
  rw [Complex.ofRealCLM.integral_comp_comm
    ((continuous_radialDerivative hg x).const_mul _).continuousOn.integrableOn_Icc,
    integral_const_mul, integral_radialDerivative hg x ha hab]
  rfl

lemma gradient_hasCompactSupport {g : ℂ → ℝ} (hc : HasCompactSupport g) :
    HasCompactSupport (gradient g) := (hc.fderiv ℝ).comp_left (map_zero _)

lemma moment_density_integrable {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (x : ℂ) :
    Integrable (fun y => star (y-x) * gradient g y) :=
  ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul (continuous_gradient hg)).integrable_of_hasCompactSupport
    (gradient_hasCompactSupport hc).mul_left

end DiskMoments

namespace DiskKernels

/-- Only integrability over the largest supporting disk is required. -/
theorem kernel_pairing_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x : ℂ)
    {f : ℂ → E} (hf : IntegrableOn f (Metric.ball x b)) :
    (∫ y, kernel k x y • f y) = ∫ t, k t • ∫ y in Metric.ball x t, f y := by
  have hh := kernel_pairing k x (hf.integrable_indicator measurableSet_ball)
  have hleft : (fun y => kernel k x y • (Metric.ball x b).indicator f y) =
      fun y => kernel k x y • f y := by
    funext y
    by_cases hy : y ∈ Metric.ball x b
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, kernel_zero k x hy, zero_smul, zero_smul]
  rw [hleft] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Icc a b
  · congr 1
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    exact Set.indicator_of_mem (show y ∈ Metric.ball x b from lt_of_lt_of_le hy ht.2) f
  · rw [k.support t ht, zero_smul, zero_smul]

end DiskKernels

namespace DiskMoments
open DiskKernels

/-- A faithful balanced disk-mixture kernel, with an explicit absolute bound. -/
theorem balanced_kernel {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ)
    {r δ : ℝ} (hr : r ∈ Icc (1 : ℝ) 2) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hm : signedAverage g x (r-δ) ≤ signedAverage g x r)
    (hp : signedAverage g x (r+δ) ≤ signedAverage g x r) :
    ∃ k : RadiusDensity (r-δ) (r+δ) ⟨216/δ, by positivity⟩,
      (∫ y, kernel k x y • (star (y-x) * gradient g y)) = 0 := by
  have ha : (1 : ℝ)/2 ≤ r-δ := by linarith [hr.1]
  have hb : r+δ ≤ (3 : ℝ) := by linarith [hr.2]
  have hrh : (1 : ℝ)/2 ≤ r := by linarith [hr.1]
  have hrb : r ≤ (3 : ℝ) := by linarith [hr.2]
  have hmr : r-δ < r := by linarith
  have hpr : r < r+δ := by linarith
  let km : RadiusDensity (r-δ) (r+δ) ⟨216/δ, by positivity⟩ :=
    enlarge (inverseCubeDensity (r-δ) r ha hrb hmr) le_rfl hpr.le (by
      change 216/(r-(r-δ)) ≤ 216/δ
      simp)
  let kp : RadiusDensity (r-δ) (r+δ) ⟨216/δ, by positivity⟩ :=
    enlarge (inverseCubeDensity r (r+δ) hrh hb hpr) hmr.le le_rfl (by
      change 216/(r+δ-r) ≤ 216/δ
      simp)
  let A := Real.pi / cubeMass (r-δ) r * (signedAverage g x r - signedAverage g x (r-δ))
  let B := Real.pi / cubeMass r (r+δ) * (signedAverage g x (r+δ) - signedAverage g x r)
  have hA : 0 ≤ A := mul_nonneg (div_nonneg Real.pi_pos.le (cubeMass_pos ha hrb hmr).le)
    (sub_nonneg.mpr hm)
  have hB : B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg Real.pi_pos.le (cubeMass_pos hrh hb hpr).le) (sub_nonpos.mpr hp)
  obtain ⟨w, hw0, hw1, hw⟩ := convex_zero hA hB
  let k := mix km kp w hw0 hw1
  refine ⟨k, ?_⟩
  have hfi : IntegrableOn (fun y => star (y-x) * gradient g y) (Metric.ball x (r+δ)) :=
    (((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul (continuous_gradient hg)).continuousOn.integrableOn_compact (isCompact_closedBall x (r+δ))).mono_set Metric.ball_subset_closedBall
  rw [kernel_pairing_local k x hfi]
  change (∫ t, (w * cubeDensity (r-δ) r t + (1-w) * cubeDensity r (r+δ) t) • moment g x t) = 0
  simp_rw [add_smul, mul_smul]
  have him : Integrable (fun t : ℝ => w • (cubeDensity (r-δ) r t • moment g x t)) := by
    convert! (cubeDensity_moment_integrable hg x (a := r-δ) (b := r) (by linarith [ha])).smul w
  have hip : Integrable (fun t : ℝ => (1-w) • (cubeDensity r (r+δ) t • moment g x t)) := by
    convert! (cubeDensity_moment_integrable hg x (a := r) (b := r+δ) (by linarith [hr.1])).smul (1-w)
  rw [integral_add him hip,
    integral_smul, integral_smul,
    cubeDensity_moment_integral hg x (by linarith [ha]) hmr.le,
    cubeDensity_moment_integral hg x (by linarith [hr.1]) hpr.le]
  change w • (A : ℂ) + (1-w) • (B : ℂ) = 0
  apply Complex.ext <;> simp only [Complex.smul_re, Complex.smul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.zero_re, Complex.zero_im,
    smul_eq_mul, mul_zero, add_zero]
  exact hw

end DiskMoments

end
end

end OAI
