import Mathlib
import OAI.Analysis.SymmetricDomains.CompactFaithfulIsotropy

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology Metric MeasureTheory
open scoped Classical

theorem finite_measure_holomorphic_average_derivative {K : Type*} [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] {n m : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (F : K → Affine n → Affine m)
    (ha : ∀ a, AnalyticOnNhd ℂ (F a) U)
    (hc : ∀ x ∈ U, Continuous (fun a => F a x))
    (hdc : ∀ x ∈ U, Continuous (fun a => fderiv ℂ (F a) x))
    {M : ℝ} (hM : ∀ a, ∀ x ∈ U, ‖F a x‖ ≤ M)
    {p : Affine n} (hp : p ∈ U) :
    HasFDerivAt (fun x => ∫ a, F a x ∂μ) (∫ a, fderiv ℂ (F a) p ∂μ) p := by
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  have hsub : ∀ x ∈ ball p (R/2), ball x (R/2) ⊆ U := by
    intro x hx y hy
    apply hball
    rw [mem_ball] at *
    exact (dist_triangle y x p).trans_lt (by linarith)
  have hbound : ∀ a, ∀ x ∈ ball p (R/2), ‖fderiv ℂ (F a) x‖ ≤ (2*M)/(R/2) := by
    intro a x hx
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
      ((ha a).differentiableOn.mono (hsub x hx)) _ (by linarith)
    intro y hy
    rw [mem_closedBall,dist_eq_norm]
    have hxU := hsub x hx (mem_ball_self (by linarith))
    exact (norm_sub_le _ _).trans (by linarith [hM a y (hsub x hx hy),hM a x hxU])
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => (2*M)/(R/2))
    (ball_mem_nhds p (by linarith : 0<R/2))
  · filter_upwards [hU.mem_nhds hp] with x hx
    exact (hc x hx).aestronglyMeasurable
  · exact ⟨(hc p hp).aestronglyMeasurable,HasFiniteIntegral.of_bounded (ae_of_all μ (fun a => hM a p hp))⟩
  · exact (hdc p hp).aestronglyMeasurable
  · exact ae_of_all μ hbound
  · exact integrable_const _
  · exact ae_of_all μ (fun a x hx => (ha a _ (hsub x hx (mem_ball_self (by linarith)))).differentiableAt.hasFDerivAt)

theorem finite_measure_holomorphic_average_analytic {K : Type*} [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] {n m : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (F : K → Affine n → Affine m)
    (ha : ∀ a, AnalyticOnNhd ℂ (F a) U)
    (hc : ∀ x ∈ U, Continuous (fun a => F a x))
    (hdc : ∀ x ∈ U, Continuous (fun a => fderiv ℂ (F a) x))
    {M : ℝ} (hM : ∀ a, ∀ x ∈ U, ‖F a x‖ ≤ M) :
    AnalyticOnNhd ℂ (fun x => ∫ a, F a x ∂μ) U := by
  apply analyticOnNhd_of_differentiableOn_affine hU
  intro p hp
  exact (finite_measure_holomorphic_average_derivative μ hU F ha hc hdc hM hp).differentiableAt.differentiableWithinAt

end

open Set Filter Topology Metric MeasureTheory
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
variable (a : ℝ → Biholomorph U U) (ha : Continuous a)

def shortTimeAverage (r : ℝ) (x : Affine n) : Affine n :=
  r⁻¹ • ∫ t in 0..r, (a t).ambientAut x

include ha
omit [LocallyCompactSpace U] in
theorem oneParameter_evaluation_continuous (x : U) :
    Continuous (fun t => (a t).toHomeomorph x) := (continuous_evaluation x).comp ha

include hU
theorem shortTimeAverage_derivative (hb : Bornology.IsBounded U) {r : ℝ} (hr : 0<r)
    {p : Affine n} (hp : p ∈ U) :
    HasFDerivAt (shortTimeAverage a r)
      (r⁻¹ • ∫ t in 0..r, (a t).derivativeAt ⟨p,hp⟩) p := by
  obtain ⟨M,hM,hMb⟩ := hb.exists_pos_norm_le
  have hv : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) r)) :=
    ⟨by simp [Real.volume_Ioc]⟩
  have hd := finite_measure_holomorphic_average_derivative
    (M := M) (volume.restrict (Ioc (0 : ℝ) r)) hU (fun t => (a t).ambientAut)
    (fun t => (a t).ambientAut_analytic hU)
    (fun x hx => by
      have h := continuous_subtype_val.comp (oneParameter_evaluation_continuous a ha ⟨x,hx⟩)
      simpa only [Function.comp_def,← ambientAut_apply] using h)
    (fun x hx => (derivativeAt_continuous hU ⟨x,hx⟩).comp ha)
    (fun t x hx => by
      rw [ambientAut_apply (a t) ⟨x,hx⟩]
      exact hMb _ ((a t).toHomeomorph ⟨x,hx⟩).property) hp
  unfold shortTimeAverage
  convert! hd.const_smul r⁻¹ using 1 <;> simp only [intervalIntegral.integral_of_le hr.le,derivativeAt]
  rfl

theorem shortTimeAverage_analytic (hb : Bornology.IsBounded U) {r : ℝ} (hr : 0<r) :
    AnalyticOnNhd ℂ (shortTimeAverage a r) U := by
  apply analyticOnNhd_of_differentiableOn_affine hU
  intro p hp
  exact (shortTimeAverage_derivative hU a ha hb hr hp).differentiableAt.differentiableWithinAt

theorem shortTimeAverage_linear_tendsto (hzero : a 0=1) (p : U) :
    Tendsto (fun r : ℝ => r⁻¹ • ∫ t in 0..r, (a t).derivativeAt p)
      (𝓝[>] 0) (𝓝 (1 : Affine n →L[ℂ] Affine n)) := by
  have hc := (derivativeAt_continuous hU p).comp ha
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 0) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : (a 0).derivativeAt p=(1 : Affine n →L[ℂ] Affine n) := by
    rw [hzero,derivativeAt_one hU]
  simpa only [Function.comp_def,zero_add,intervalIntegral.integral_same,sub_zero,he] using hd.tendsto_slope_zero_right

omit hU [LocallyCompactSpace U] in

theorem shortTimeAverage_orbit_derivative
    (hmul : ∀ s t, a (s+t)=a s*a t) (r : ℝ) (p : U) (s : ℝ) :
    HasDerivAt (fun t => shortTimeAverage a r ((a t).toHomeomorph p).val)
      (r⁻¹ • (((a (r+s)).toHomeomorph p).val-((a s).toHomeomorph p).val)) s := by
  let f : ℝ → Affine n := fun t => ((a t).toHomeomorph p).val
  have hc : Continuous f := continuous_subtype_val.comp (oneParameter_evaluation_continuous a ha p)
  have he (t : ℝ) : shortTimeAverage a r ((a t).toHomeomorph p).val =
      r⁻¹ • ∫ v in t..r+t, f v := by
    unfold shortTimeAverage
    congr 1
    have h (u : ℝ) : (a u).ambientAut ((a t).toHomeomorph p).val = f (u+t) := by
      dsimp only [f]
      rw [ambientAut_apply,hmul]
      rfl
    simp_rw [h]
    simpa only [zero_add] using intervalIntegral.integral_comp_add_right (a := 0) (b := r) f t
  simp_rw [he]
  have hd := intervalIntegral.integral_hasFDerivAt (hc.intervalIntegrable s (r+s))
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.stronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt hc.continuousAt
  have hg : HasDerivAt (fun t : ℝ => (t,r+t)) (1,1) s :=
    (hasDerivAt_id s).prodMk ((hasDerivAt_id s).const_add r)
  convert! (hd.comp_hasDerivAt s hg).const_smul r⁻¹ using 1
  ·
    simp only [FunLike.coe_sub,Pi.sub_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd',ContinuousLinearMap.coe_fst',one_smul,f]

theorem exists_regular_shortTimeAverage (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (p : U) :
    ∃ (r : ℝ), 0<r ∧ ∃ e : Affine n ≃L[ℂ] Affine n,
      HasStrictFDerivAt (shortTimeAverage a r) (e : Affine n →L[ℂ] Affine n) p.val := by
  have ht := shortTimeAverage_linear_tendsto hU a ha hzero p
  have hu : ∀ᶠ r : ℝ in 𝓝[>] 0,
      IsUnit (r⁻¹ • ∫ t in 0..r, (a t).derivativeAt p) :=
    ht.eventually (Units.isOpen.mem_nhds isUnit_one)
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0<r := self_mem_nhdsWithin
  obtain ⟨r,hr,hunit⟩ := (hpos.and hu).exists
  have hder := shortTimeAverage_derivative hU a ha hb hr p.property
  have hu' : IsUnit (fderiv ℂ (shortTimeAverage a r) p.val) := by
    rwa [hder.fderiv]
  let e := ContinuousLinearEquiv.unitsEquiv ℂ (Affine n) hu'.unit
  refine ⟨r,hr,e,?_⟩
  have he : (e : Affine n →L[ℂ] Affine n) = fderiv ℂ (shortTimeAverage a r) p.val := hu'.unit_spec
  rw [he]
  exact (shortTimeAverage_analytic hU a ha hb hr _ p.property).hasStrictFDerivAt

omit hU [LocallyCompactSpace U] in

theorem oneParameter_hasDerivAt_of_regular_average
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t)
    (r : ℝ) (p : U) (e : Affine n ≃L[ℂ] Affine n)
    (hF : HasStrictFDerivAt (shortTimeAverage a r) (e : Affine n →L[ℂ] Affine n) p.val) :
    HasDerivAt (fun t => ((a t).toHomeomorph p).val)
      (e.symm (r⁻¹ • (((a r).toHomeomorph p).val-p.val))) 0 := by
  let F := shortTimeAverage a r
  let ψ := hF.localInverse F e p.val
  have hc : Continuous (fun t => ((a t).toHomeomorph p).val) :=
    continuous_subtype_val.comp (oneParameter_evaluation_continuous a ha p)
  have hp : ((a 0).toHomeomorph p).val=p.val := by rw [hzero,one_apply]
  have hi : ∀ᶠ t : ℝ in 𝓝 0, ψ (F ((a t).toHomeomorph p).val)=((a t).toHomeomorph p).val := by
    apply (show Tendsto (fun t => ((a t).toHomeomorph p).val) (𝓝 0) (𝓝 p.val) by
      simpa only [hp] using hc.tendsto 0) hF.eventually_left_inverse
  have ho : HasDerivAt (fun t => F ((a t).toHomeomorph p).val)
      (r⁻¹ • (((a r).toHomeomorph p).val-p.val)) 0 := by
    simpa only [add_zero,hp] using shortTimeAverage_orbit_derivative a ha hmul r p 0
  have hψ : HasFDerivAt ψ (e.symm : Affine n →L[ℂ] Affine n) (F ((a 0).toHomeomorph p).val) := by
    rw [hp]
    exact hF.to_localInverse.hasFDerivAt
  exact ((hψ.restrictScalars ℝ).comp_hasDerivAt 0 ho).congr_of_eventuallyEq (hi.mono (fun _ h => h.symm))

theorem oneParameter_differentiableAt_zero (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U) :
    DifferentiableAt ℝ (fun t => ((a t).toHomeomorph p).val) 0 := by
  obtain ⟨r,hr,e,hF⟩ := exists_regular_shortTimeAverage hU a ha hb hzero p
  exact (oneParameter_hasDerivAt_of_regular_average a ha hzero hmul r p e hF).differentiableAt

end Biholomorph
end Release061

end

end OAI
