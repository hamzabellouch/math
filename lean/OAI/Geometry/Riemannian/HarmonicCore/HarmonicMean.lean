import OAI.Geometry.Riemannian.HarmonicCore.WeakMean
import OAI.Geometry.Riemannian.HarmonicCore.DirichletOperator

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution
open Matrix
open scoped RealInnerProductSpace

namespace HarmonicCounterexample.Main

lemma smooth_upper_primitive {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (b : ℝ)
    (hηs : tsupport η ⊆ Iio b) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ deriv ψ=η ∧ tsupport ψ ⊆ Iic b := by
  let ψ : ℝ → ℝ := fun t ↦ ∫ s in b..t, η s
  have hd (t : ℝ) : HasDerivAt ψ (η t) t :=
    intervalIntegral.integral_hasDerivAt_right (hη.continuous.intervalIntegrable _ _)
      hη.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hη.continuous.continuousAt
  have he : deriv ψ=η := funext fun t ↦ (hd t).deriv
  refine ⟨ψ,contDiff_infty_iff_deriv.mpr ⟨fun t ↦ (hd t).differentiableAt,he ▸ hη⟩,he,?_⟩
  apply closure_minimal _ isClosed_Iic
  intro t ht
  by_contra hn
  have hbt : b≤t := le_of_lt (lt_of_not_ge hn)
  have hz : ψ t=0 := by
    dsimp only [ψ]
    rw [intervalIntegral.integral_of_le hbt]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    exact image_eq_zero_of_notMem_tsupport fun hh ↦ (not_lt_of_ge hs.1.le) (hηs hh)
  exact ht hz



lemma square_test_fundamental {R : ℝ} (hR : 0<R) {F : ℝ → ℝ} (hF : Continuous F)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Iio (R^2) →
      (∫ r in Ioi (0:ℝ), 2*r*deriv ψ (r^2)*F r)=0) :
    ∀ r ∈ Ioo (0:ℝ) R, F r=0 := by
  intro r hr
  obtain ⟨B,hrB,hBR⟩ := exists_between hr.2
  have hB : 0<B := hr.1.trans hrB
  let G : ℝ → ℝ := fun t ↦ F (Real.sqrt t)
  have hG : Continuous G := hF.comp Real.continuous_sqrt
  have htest (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (_hηc : HasCompactSupport η)
      (hηs : tsupport η ⊆ Ioo (0:ℝ) (B^2)) :
      (∫ t : ℝ, η t • G t)=0 := by
    obtain ⟨ψ,hψ,hψd,hψs⟩ := smooth_upper_primitive hη (B^2)
      (hηs.trans Ioo_subset_Iio_self)
    have hψR : tsupport ψ ⊆ Iio (R^2) := by
      intro t ht
      have ht' := hψs ht
      change t≤B^2 at ht'
      have hBRsq : B^2<R^2 := by nlinarith
      exact ht'.trans_lt hBRsq
    have hw := hweak ψ hψ hψR
    rw [hψd] at hw
    have he : (∫ t : ℝ, η t • G t) = ∫ t in (0:ℝ)..B^2, η t * G t := by
      rw [intervalIntegral.integral_of_le (sq_nonneg B)]
      simp only [smul_eq_mul]
      symm
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      exact Eventually.of_forall fun t ht ↦ by
        have hz : η t=0 := image_eq_zero_of_notMem_tsupport fun hh ↦
          ht ⟨(hηs hh).1,(hηs hh).2.le⟩
        rw [hz,zero_mul]
    rw [he]
    have hsub := intervalIntegral.integral_comp_mul_deriv
      (a:=0) (b:=B) (f:=fun t : ℝ ↦ t^2) (f':=fun t ↦ 2*t)
      (g:=fun t ↦ η t * G t)
      (fun t _ ↦ by convert! (hasDerivAt_id t).pow 2 using 1; simp)
      (by fun_prop) (hη.continuous.mul hG)
    simp only [zero_pow (by norm_num : (2:ℕ)≠0)] at hsub
    rw [← hsub]
    have hp : (∫ t in (0:ℝ)..B, ((fun t ↦ η t * G t) ∘ (fun t : ℝ ↦ t^2)) t * (2*t)) =
        ∫ t in (0:ℝ)..B, 2*t*η (t^2)*F t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 : 0≤t := by
        rw [uIcc_of_le hB.le] at ht
        exact ht.1
      dsimp only [Function.comp_apply,G]
      rw [Real.sqrt_sq ht0]
      ring
    rw [hp,intervalIntegral.integral_of_le hB.le]
    have hrestrict : (∫ t in Ioi (0:ℝ), 2*t*η (t^2)*F t) =
        ∫ t in Ioc (0:ℝ) B, 2*t*η (t^2)*F t := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      intro t ht
      have hBt : B<t := by
        have hnot := ht.2
        simp only [mem_Ioc,not_and,not_le] at hnot
        exact hnot ht.1
      have hz : η (t^2)=0 := image_eq_zero_of_notMem_tsupport fun hh ↦ by
        have hh' := (hηs hh).2
        nlinarith
      rw [hz,mul_zero,zero_mul]
    rw [←hrestrict,hw]
  have hae := (isOpen_Ioo : IsOpen (Ioo (0:ℝ) (B^2))).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hG.locallyIntegrable.locallyIntegrableOn (s:=Ioo (0:ℝ) (B^2))) htest
  have he : EqOn G (fun _ ↦ 0) (Ioo (0:ℝ) (B^2)) :=
    (volume : Measure ℝ).eqOn_open_of_ae_eq
      ((ae_restrict_iff' isOpen_Ioo.measurableSet).mpr hae) isOpen_Ioo
      hG.continuousOn continuous_const.continuousOn
  have hrr : r^2 ∈ Ioo (0:ℝ) (B^2) := ⟨sq_pos_of_pos hr.1,by nlinarith [hr.1]⟩
  simpa only [G,Real.sqrt_sq hr.1.le] using he hrr



theorem polar_harmonic_mean {a R : ℝ} (ha : 0<a) (hR : 0<R)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r≤1 → f r=r)
    (hb : ∀ r : ℝ, 0≤r → a*r≤ f r ∧ f r≤r)
    {u : E3 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hharm : ∀ x ∈ Metric.ball (0:E3) R,
      (polarMetric ha f H hs hc hb).laplacian u x=0) :
    ∀ r ∈ Icc (0:ℝ) R, sphericalMean u r=u 0 := by
  have hF : Continuous (fun r ↦ f r^2*sphericalMeanDerivative u r) :=
    (hs.continuous.pow 2).mul (sphericalMeanDerivative_continuous hu)
  have hflux := square_test_fundamental hR hF (fun ψ hψ hψs ↦ by
    convert polar_harmonic_weak_mean ha hR f H hs hc hb hu hharm hψ hψs using 1
    congr 1
    ext r
    ring)
  have hd : EqOn (deriv (sphericalMean u)) 0 (Ioo (0:ℝ) R) := by
    intro r hr
    change deriv (sphericalMean u) r=0
    rw [(sphericalMean_hasDerivAt hu r).deriv]
    exact (mul_eq_zero.mp (hflux r hr)).resolve_left
      (pow_ne_zero 2 ((mul_pos ha hr.1).trans_le (hb r hr.1.le).1).ne')
  obtain ⟨c,hcst⟩ := (isOpen_Ioo : IsOpen (Ioo (0:ℝ) R)).exists_is_const_of_deriv_eq_zero
    isPreconnected_Ioo (fun r _ ↦ (sphericalMean_hasDerivAt hu r).differentiableAt.differentiableWithinAt) hd
  have he : EqOn (sphericalMean u) (fun _ ↦ c) (Ioo (0:ℝ) R) := hcst
  have hcl := he.closure (sphericalMean_continuous hu.continuous) continuous_const
  rw [closure_Ioo hR.ne] at hcl
  have h0 := hcl (show (0:ℝ) ∈ Icc (0:ℝ) R from ⟨le_rfl,hR.le⟩)
  rw [sphericalMean_zero] at h0
  intro r hr
  exact (hcl hr).trans h0.symm



lemma sphericalMean_continuousOn {R : ℝ} {u : E3 → ℝ}
    (hu : ContinuousOn u (Metric.closedBall (0:E3) R)) :
    ContinuousOn (sphericalMean u) (Icc (0:ℝ) R) := by
  let V : (Icc (0:ℝ) R) × UnitSphere3 → Metric.closedBall (0:E3) R := fun p ↦
    ⟨(p.1:ℝ) • (p.2:E3),by
      have hz : ‖(p.2:E3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.2.property
      simpa only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg p.1.property.1,hz,mul_one] using p.1.property.2⟩
  have hV : Continuous V := by dsimp [V]; fun_prop
  have hh : Continuous (fun p : (Icc (0:ℝ) R) × UnitSphere3 ↦ u ((p.1:ℝ) • (p.2:E3))) :=
    hu.domRestrict.comp hV
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun r : Icc (0:ℝ) R ↦ ∫ z : UnitSphere3, u ((r:ℝ) • (z:E3)) ∂angularMeasure)
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ:=angularMeasure)
      (f:=fun r : Icc (0:ℝ) R ↦ fun z : UnitSphere3 ↦ u ((r:ℝ) • (z:E3))) hh isCompact_univ)

theorem polar_harmonic_mean_closedBall {a R : ℝ} (ha : 0<a) (hR : 0<R)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r≤1 → f r=r)
    (hb : ∀ r : ℝ, 0≤r → a*r≤ f r ∧ f r≤r)
    {u : E3 → ℝ} (hu : ContDiffOn ℝ ∞ u (Metric.ball (0:E3) R))
    (huc : ContinuousOn u (Metric.closedBall (0:E3) R))
    (hharm : ∀ x ∈ Metric.ball (0:E3) R,
      (polarMetric ha f H hs hc hb).laplacian u x=0) :
    ∀ r ∈ Icc (0:ℝ) R, sphericalMean u r=u 0 := by
  have he : EqOn (sphericalMean u) (fun _ ↦ u 0) (Ioo (0:ℝ) R) := by
    intro r hr
    let s := (r+R)/2
    have hrs : r<s := by dsimp [s]; linarith [hr.2]
    have hsR : s<R := by dsimp [s]; linarith [hr.2]
    have hs0 : 0<s := hr.1.trans hrs
    obtain ⟨K,hK⟩ := SmoothMetric3.compact_smooth_restriction s R hs0 hsR hu
    have hKh : ∀ x ∈ Metric.ball (0:E3) s,
        (polarMetric ha f H hs hc hb).laplacian (K:E3 → ℝ) x=0 := by
      intro x hx
      rw [(polarMetric ha f H hs hc hb).laplacian_congr_nhds
        (hK.eventuallyEq_of_mem (Metric.closedBall_mem_nhds_of_mem hx))]
      exact hharm x (Metric.ball_subset_ball hsR.le hx)
    have hm := polar_harmonic_mean ha hs0 f H hs hc hb K.property.1 hKh r ⟨hr.1.le,hrs.le⟩
    have h0 := hK (show (0:E3) ∈ Metric.closedBall 0 s by simp [hs0.le])
    rw [h0] at hm
    rw [←hm]
    apply integral_congr_ae
    filter_upwards with z
    symm
    apply hK
    have hz : ‖(z:E3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using z.property
    simpa only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg hr.1.le,hz,mul_one] using hrs.le
  exact he.of_subset_closure (sphericalMean_continuousOn huc) continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hR.ne])

theorem polar_dirichlet_mean {a R : ℝ} (ha : 0<a) (hR : 0<R)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r≤1 → f r=r)
    (hb : ∀ r : ℝ, 0≤r → a*r≤ f r ∧ f r≤r)
    (F : SmoothMetric3.CompactSmoothData) {r : ℝ} (hr : r ∈ Icc (0:ℝ) R) :
    sphericalMean ((polarMetric ha f H hs hc hb).classicalExtension R hR F) r=
      sphericalMean (F:E3 → ℝ) R := by
  let g := polarMetric ha f H hs hc hb
  obtain ⟨huc,hu,hbd,hL⟩ := g.classicalExtension_spec R hR F
  have hm := polar_harmonic_mean_closedBall ha hR f H hs hc hb hu huc hL
  rw [hm r hr,←hm R ⟨hR.le,le_rfl⟩]
  apply integral_congr_ae
  filter_upwards with z
  apply hbd
  have hz : ‖(z:E3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using z.property
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hR.le,hz,mul_one]

end HarmonicCounterexample.Main

end

end OAI
