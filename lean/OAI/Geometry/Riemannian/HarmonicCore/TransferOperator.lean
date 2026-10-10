import OAI.Geometry.Riemannian.HarmonicCore.MeanContraction
import OAI.Geometry.Riemannian.HarmonicCore.BoundaryTrace

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

noncomputable def sphereInClosedBall (r R : ℝ) (hr : r ∈ Icc (0:ℝ) R) :
    C(UnitSphere3,Metric.closedBall (0:E3) R) where
  toFun z := ⟨r • (z:E3),by
    have hz : ‖(z:E3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using z.property
    simpa only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg hr.1,hz,mul_one] using hr.2⟩
  continuous_toFun := by fun_prop

namespace SmoothMetric3
noncomputable def radiusDirichlet (g : SmoothMetric3) (r R : ℝ) (hR : 0<R)
    (hr : r ∈ Icc (0:ℝ) R) : CompactSmoothData →ₗ[ℝ] C(UnitSphere3,ℝ) :=
  (ContinuousMap.compCLM ℝ ℝ (sphereInClosedBall r R hr)).toLinearMap.comp (g.ballDirichlet R hR)

noncomputable def radiusDirichletL2 (g : SmoothMetric3) (r R : ℝ) (hR : 0<R)
    (hr : r ∈ Icc (0:ℝ) R) : CompactSmoothData →ₗ[ℝ] Lp ℝ 2 angularMeasure :=
  (ContinuousMap.toLp 2 angularMeasure ℝ).toLinearMap.comp (g.radiusDirichlet r R hR hr)
end SmoothMetric3

lemma polar_radiusDirichletL2_norm_le {a R r : ℝ} (ha : 0<a) (hR : 0<R)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r≤1 → f r=r)
    (hb : ∀ r : ℝ, 0≤r → a*r≤ f r ∧ f r≤r)
    (hr : r ∈ Icc (0:ℝ) R) (F : SmoothMetric3.CompactSmoothData) :
    ‖(polarMetric ha f H hs hc hb).radiusDirichletL2 r R hR hr F‖ ≤
      ‖SmoothMetric3.radiusTraceL2 R F‖ := by
  have ho := continuous_toL2_norm_sq ((polarMetric ha f H hs hc hb).radiusDirichlet r R hR hr F)
  have hi := radiusTraceL2_norm_sq R F
  have hh := polar_dirichlet_L2_contraction ha hR f H hs hc hb F hr
  change ‖(polarMetric ha f H hs hc hb).radiusDirichletL2 r R hR hr F‖^2 =
    (∫ z : UnitSphere3,
      ((polarMetric ha f H hs hc hb).classicalExtension R hR F (r • (z:E3)))^2 ∂angularMeasure) at ho
  change (∫ z : UnitSphere3,
    ((polarMetric ha f H hs hc hb).classicalExtension R hR F (r • (z:E3)))^2 ∂angularMeasure)≤_ at hh
  nlinarith [norm_nonneg ((polarMetric ha f H hs hc hb).radiusDirichletL2 r R hR hr F),
    norm_nonneg (SmoothMetric3.radiusTraceL2 R F)]

noncomputable def wholeBallL2 {a R r : ℝ} (ha : 0<a) (hR : 0<R)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r≤1 → f r=r)
    (hb : ∀ r : ℝ, 0≤r → a*r≤ f r ∧ f r≤r)
    (hr : r ∈ Icc (0:ℝ) R) : Lp ℝ 2 angularMeasure →L[ℝ] Lp ℝ 2 angularMeasure :=
  ((polarMetric ha f H hs hc hb).radiusDirichletL2 r R hR hr).extendOfNorm
    (SmoothMetric3.radiusTraceL2 R)

lemma wholeBallL2_on_smooth {a R r : ℝ} (ha : 0<a) (hR : 0<R)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r≤1 → f r=r)
    (hb : ∀ r : ℝ, 0≤r → a*r≤ f r ∧ f r≤r)
    (hr : r ∈ Icc (0:ℝ) R) (F : SmoothMetric3.CompactSmoothData) :
    wholeBallL2 ha hR f H hs hc hb hr (SmoothMetric3.radiusTraceL2 R F)=
      (polarMetric ha f H hs hc hb).radiusDirichletL2 r R hR hr F := by
  exact LinearMap.extendOfNorm_eq (SmoothMetric3.radiusTraceL2_dense R hR)
    ⟨1,fun F ↦ by simpa only [one_mul] using polar_radiusDirichletL2_norm_le ha hR f H hs hc hb hr F⟩ F

theorem wholeBallL2_norm_le {a R r : ℝ} (ha : 0<a) (hR : 0<R)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r≤1 → f r=r)
    (hb : ∀ r : ℝ, 0≤r → a*r≤ f r ∧ f r≤r)
    (hr : r ∈ Icc (0:ℝ) R) (v : Lp ℝ 2 angularMeasure) :
    ‖wholeBallL2 ha hR f H hs hc hb hr v‖ ≤ ‖v‖ := by
  simpa only [one_mul,wholeBallL2] using LinearMap.norm_extendOfNorm_apply_le
    (f := (polarMetric ha f H hs hc hb).radiusDirichletL2 r R hR hr)
    (SmoothMetric3.radiusTraceL2_dense R hR) 1
    (fun F ↦ by simpa only [one_mul] using polar_radiusDirichletL2_norm_le ha hR f H hs hc hb hr F) v


noncomputable def angularOneL2 : Lp ℝ 2 angularMeasure :=
  ContinuousMap.toLp 2 angularMeasure ℝ (1:C(UnitSphere3,ℝ))

lemma angularOneL2_inner (v : Lp ℝ 2 angularMeasure) :
    ⟪angularOneL2,v⟫_ℝ = ∫ z, v z ∂angularMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℝ) angularMeasure (1:C(UnitSphere3,ℝ))] with z hz
  change angularOneL2 z=1 at hz
  simp only [hz,RCLike.inner_apply,map_one,mul_one]

lemma continuous_toL2_mean (F : C(UnitSphere3,ℝ)) :
    ⟪angularOneL2,ContinuousMap.toLp 2 angularMeasure ℝ F⟫_ℝ = ∫ z, F z ∂angularMeasure := by
  rw [angularOneL2_inner]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℝ) angularMeasure F)

theorem wholeBallL2_mean {a R r : ℝ} (ha : 0<a) (hR : 0<R)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r≤1 → f r=r)
    (hb : ∀ r : ℝ, 0≤r → a*r≤ f r ∧ f r≤r)
    (hr : r ∈ Icc (0:ℝ) R) (v : Lp ℝ 2 angularMeasure) :
    (∫ z, wholeBallL2 ha hR f H hs hc hb hr v z ∂angularMeasure)=∫ z, v z ∂angularMeasure := by
  rw [←angularOneL2_inner,←angularOneL2_inner]
  refine DenseRange.induction_on (SmoothMetric3.radiusTraceL2_dense R hR) v
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro F
  rw [wholeBallL2_on_smooth]
  change ⟪angularOneL2,ContinuousMap.toLp 2 angularMeasure ℝ
    ((polarMetric ha f H hs hc hb).radiusDirichlet r R hR hr F)⟫_ℝ =
    ⟪angularOneL2,ContinuousMap.toLp 2 angularMeasure ℝ (SmoothMetric3.radiusTrace R F)⟫_ℝ
  rw [continuous_toL2_mean,continuous_toL2_mean]
  exact polar_dirichlet_mean ha hR f H hs hc hb F hr

theorem wholeBallL2_one {a R r : ℝ} (ha : 0<a) (hR : 0<R)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r≤1 → f r=r)
    (hb : ∀ r : ℝ, 0≤r → a*r≤ f r ∧ f r≤r)
    (hr : r ∈ Icc (0:ℝ) R) :
    wholeBallL2 ha hR f H hs hc hb hr angularOneL2=angularOneL2 := by
  let F := SmoothMetric3.boundaryUnit R hR
  have hF : SmoothMetric3.radiusTrace R F=1 := by
    ext z
    apply SmoothMetric3.boundaryUnit_eq
    have hz : ‖(z:E3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using z.property
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hR.le,hz,mul_one]
  have htrace : SmoothMetric3.radiusTraceL2 R F=angularOneL2 := by
    change ContinuousMap.toLp 2 angularMeasure ℝ (SmoothMetric3.radiusTrace R F)=_
    rw [hF]; rfl
  rw [←htrace,wholeBallL2_on_smooth]
  change ContinuousMap.toLp 2 angularMeasure ℝ
    ((polarMetric ha f H hs hc hb).radiusDirichlet r R hR hr F)=
    ContinuousMap.toLp 2 angularMeasure ℝ (SmoothMetric3.radiusTrace R F)
  rw [hF]
  congr 1
  ext z
  exact (polarMetric ha f H hs hc hb).ballDirichlet_constant R hR F 1
    (SmoothMetric3.boundaryUnit_eq R hR) (sphereInClosedBall r R hr z)


theorem wholeBallL2_restriction {a r s R : ℝ} (ha : 0<a) (hr : 0<r)
    (hrs : r<s) (hsR : s<R)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hf : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r≤1 → f r=r)
    (hb : ∀ r : ℝ, 0≤r → a*r≤ f r ∧ f r≤r)
    (v : Lp ℝ 2 angularMeasure) :
    wholeBallL2 ha (hr.trans hrs) f H hf hc hb ⟨hr.le,hrs.le⟩
      (wholeBallL2 ha ((hr.trans hrs).trans hsR) f H hf hc hb ⟨(hr.trans hrs).le,hsR.le⟩ v)=
    wholeBallL2 ha ((hr.trans hrs).trans hsR) f H hf hc hb ⟨hr.le,(hrs.trans hsR).le⟩ v := by
  let g := polarMetric ha f H hf hc hb
  have hS : 0<s := hr.trans hrs
  have hR : 0<R := hS.trans hsR
  refine DenseRange.induction_on (SmoothMetric3.radiusTraceL2_dense R hR) v
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro F
  obtain ⟨K,hK,he⟩ := g.exact_dirichlet_restriction s R hS hsR F
  have htrace : SmoothMetric3.radiusTraceL2 s K = g.radiusDirichletL2 s R hR ⟨hS.le,hsR.le⟩ F := by
    change ContinuousMap.toLp 2 angularMeasure ℝ (SmoothMetric3.radiusTrace s K)=
      ContinuousMap.toLp 2 angularMeasure ℝ (g.radiusDirichlet s R hR ⟨hS.le,hsR.le⟩ F)
    congr 1
    ext z
    apply hK
    have hz : ‖(z:E3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using z.property
    simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hS.le,hz,mul_one,le_refl]
  erw [wholeBallL2_on_smooth,←htrace,wholeBallL2_on_smooth,wholeBallL2_on_smooth]
  change ContinuousMap.toLp 2 angularMeasure ℝ (g.radiusDirichlet r s hS ⟨hr.le,hrs.le⟩ K)=
    ContinuousMap.toLp 2 angularMeasure ℝ (g.radiusDirichlet r R hR ⟨hr.le,(hrs.trans hsR).le⟩ F)
  congr 1
  ext z
  apply he
  change r • (z:E3) ∈ Metric.closedBall (0:E3) s
  have hz : ‖(z:E3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using z.property
  simpa only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg hr.le,hz,mul_one] using hrs.le

end HarmonicCounterexample.Main

end

end OAI
