import Mathlib
import OAI.Analysis.Conductivity.Sobolev.IntervalTraceEnergy
import OAI.Analysis.Conductivity.Variational.RadialLaplacian
import OAI.Analysis.Conductivity.Sobolev.KernelParamDerivative

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set Filter Topology MeasureTheory Laplacian InnerProductSpace
open scoped Convolution

lemma radialEta_joint_smooth : ContDiffOn ℝ (↑(⊤ : ℕ∞))
    (Function.uncurry (radialEta radialProfile)) (Ioi 0 ×ˢ univ) := by
  apply ContDiffOn.div
  · exact radialProfile_smooth.comp_contDiffOn
      ((normsq_smooth.comp contDiff_snd).contDiffOn.div
        (contDiff_fst.pow 2).contDiffOn (fun p hp => pow_ne_zero _ (ne_of_gt hp.1)))
  · exact (contDiff_fst.pow 3).contDiffOn
  · intro p hp
    exact pow_ne_zero _ (ne_of_gt hp.1)

lemma laplacian_sub_right (f : WeylSpace → ℝ) (a y : WeylSpace) :
    Δ (fun z => f (z-a)) y=Δ f (y-a) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_comp_sub]

lemma radialTheta_laplacian_sub_left (s : ℝ) (x y : WeylSpace) :
    Δ (fun z => radialTheta radialProfilePrimitive s (x-z)) y=
      Δ (radialTheta radialProfilePrimitive s) (x-y) := by
  have he : (fun z => radialTheta radialProfilePrimitive s (x-z))=
      (fun z => radialTheta radialProfilePrimitive s (z-x)) := by
    ext z
    simp only [radialTheta,norm_sub_rev]
  rw [he,laplacian_sub_right]
  by_cases hs : s=0
  · subst s
    have hz : radialTheta radialProfilePrimitive 0=(fun _ : WeylSpace => (0:ℝ)) := by
      ext z
      simp [radialTheta]
    rw [hz]
    simp only [laplacian_const,Pi.zero_apply]
  · rw [radialTheta_laplacian radialProfilePrimitive_deriv
      (fun t => (radialProfile_smooth.differentiable (by simp) t).hasDerivAt) hs,
      radialTheta_laplacian radialProfilePrimitive_deriv
      (fun t => (radialProfile_smooth.differentiable (by simp) t).hasDerivAt) hs]
    simp only [norm_sub_rev]

def WeaklyHarmonicOn (f : WeylSpace → ℝ) (U : Set WeylSpace) : Prop :=
  ∀ ψ : WeylSpace → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
    tsupport ψ⊆U → (∫ y, f y*Δ ψ y)=0

def radialMollify (f : WeylSpace → ℝ) (s : ℝ) : WeylSpace → ℝ :=
  f ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] radialEta radialProfile s

lemma radialMollify_smooth {f : WeylSpace → ℝ} (hf : LocallyIntegrable f)
    {s : ℝ} (hs : 0<s) : ContDiff ℝ (↑(⊤ : ℕ∞)) (radialMollify f s) :=
  (radialEta_compact hs).contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hf (radialEta_smooth s)

lemma radialMollify_hasDerivAt {f : WeylSpace → ℝ} (hf : LocallyIntegrable f)
    {s : ℝ} (hs : 0<s) (x : WeylSpace) :
    HasDerivAt (fun r => radialMollify f r x)
      (∫ y, f y*Δ (radialTheta radialProfilePrimitive s) (x-y)) s := by
  apply convolution_param_hasDerivAt hf isOpen_Ioo (isCompact_closedBall (0:WeylSpace) (2*s))
    (S := Ioo (s/2) (2*s))
  · apply (radialEta_joint_smooth.of_le (by simp)).mono
    rintro ⟨r,y⟩ ⟨⟨hr₁,hr₂⟩,_⟩
    exact ⟨(half_pos hs).trans hr₁,mem_univ _⟩
  · intro r y hr hy
    apply radialEta_zero (by linarith [hr.1])
    have hn : 2*s<‖y‖ := by simpa [Metric.mem_closedBall,dist_zero_right] using hy
    exact hr.2.le.trans hn.le
  · constructor <;> linarith
  · intro y
    exact radial_scale_laplacian radialProfilePrimitive_deriv
      (fun t => (radialProfile_smooth.differentiable (by simp) t).hasDerivAt) hs.ne' y

lemma radialMollify_hasDerivAt_zero {f : WeylSpace → ℝ} (hf : LocallyIntegrable f)
    {U : Set WeylSpace} (hw : WeaklyHarmonicOn f U)
    {s : ℝ} (hs : 0<s) {x : WeylSpace} (hx : Metric.closedBall x s⊆U) :
    HasDerivAt (fun r => radialMollify f r x) 0 s := by
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y => radialTheta radialProfilePrimitive s (x-y)) :=
    (radialTheta_smooth s).comp (contDiff_const.sub contDiff_id)
  have hc : HasCompactSupport (fun y => radialTheta radialProfilePrimitive s (x-y)) :=
    (radialTheta_compact hs).comp_homeomorph (Homeomorph.subLeft x)
  have hv : tsupport (fun y => radialTheta radialProfilePrimitive s (x-y))⊆Metric.closedBall x s := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    rw [Metric.mem_closedBall,dist_eq_norm]
    by_contra hn
    exact hy (radialTheta_zero hs (by simpa only [norm_sub_rev] using (not_le.mp hn).le))
  have he := hw _ hψ hc (hv.trans hx)
  simp_rw [radialTheta_laplacian_sub_left] at he
  simpa only [he] using radialMollify_hasDerivAt hf hs x

theorem radialMollify_scale_independent {f : WeylSpace → ℝ} (hf : LocallyIntegrable f)
    {U : Set WeylSpace} (hw : WeaklyHarmonicOn f U) {x : WeylSpace}
    {R : ℝ} (hR : Metric.closedBall x R⊆U) {s t : ℝ}
    (hs : 0<s ∧ s<R) (ht : 0<t ∧ t<R) : radialMollify f s x=radialMollify f t x := by
  have hd (r : ℝ) (hr : r∈Ioo 0 R) : HasDerivAt (fun a => radialMollify f a x) 0 r :=
    radialMollify_hasDerivAt_zero hf hw hr.1
      ((Metric.closedBall_subset_closedBall hr.2.le).trans hR)
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0:ℝ) R).isPreconnected
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs ht

end

open Set MeasureTheory

lemma probability_integral_sq_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, f x^2 ∂μ := by
  simpa using integral_sq_le_mass_mul (hf.integrable (by norm_num)) hf.integrable_sq

theorem memLp_probability_average {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [SFinite ν]
    {f : X×Y → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun y => ∫ x, f (x,y) ∂μ) 2 ν ∧
    (∫ y, (∫ x, f (x,y) ∂μ)^2 ∂ν) ≤ ∫ z, f z^2 ∂(μ.prod ν) := by
  have hm := hf.aestronglyMeasurable.prod_swap.integral_prod_right'
  have hi := hf.integrable_sq
  have hs : ∀ᵐ y ∂ν, (∫ x, f (x,y) ∂μ)^2 ≤ ∫ x, f (x,y)^2 ∂μ := by
    filter_upwards [hi.prod_left_ae,hf.aestronglyMeasurable.prodMk_right] with y hy hmy
    exact probability_integral_sq_le ((memLp_two_iff_integrable_sq hmy).mpr hy)
  have hia : Integrable (fun y => (∫ x, f (x,y) ∂μ)^2) ν := by
    apply hi.integral_prod_right.mono' (hm.pow 2)
    filter_upwards [hs] with y hy
    change ‖(∫ x, f (x,y) ∂μ)^2‖ ≤ ∫ x, f (x,y)^2 ∂μ
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (∫ x, f (x,y) ∂μ))] using hy
  refine ⟨(memLp_two_iff_integrable_sq hm).mpr hia,?_⟩
  calc
    _ ≤ ∫ y, ∫ x, f (x,y)^2 ∂μ ∂ν := integral_mono_ae hia hi.integral_prod_right hs
    _ = _ := (integral_prod_symm _ hi).symm

end ScalarConductivity

end

end OAI
