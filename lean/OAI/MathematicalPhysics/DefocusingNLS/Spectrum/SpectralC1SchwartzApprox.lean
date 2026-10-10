import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! Approximation of a C1 radial function and its derivative on a fixed ball. -/

open Set Filter MeasureTheory
open scoped SchwartzMap ContDiff Topology
namespace DefocusingNLS

theorem spectralSmoothPrimitive (c : ℂ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    let P := fun r => c+∫ x in (0 : ℝ)..r, g x
    ContDiff ℝ ∞ P ∧ ∀ r, deriv P r=g r := by
  intro P
  have hd (r : ℝ) : HasDerivAt P (g r) r := by
    exact (intervalIntegral.integral_hasDerivAt_right
      (hg.continuous.intervalIntegrable 0 r)
      hg.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuous.continuousAt).const_add c
  have he : deriv P=g := funext (fun r => (hd r).deriv)
  exact ⟨contDiff_infty_iff_deriv.mpr
    ⟨fun r => (hd r).differentiableAt,by simpa only [he] using hg⟩,fun r => (hd r).deriv⟩

theorem spectralPrimitiveApprox_bound (f g : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hg : Continuous g) (R ε : ℝ) (hε : 0 ≤ ε)
    (he : ∀ r ∈ Icc 0 R, ‖g r-deriv f r‖ ≤ ε) (r : ℝ) (hr : r ∈ Icc 0 R) :
    ‖(f 0+∫ x in (0 : ℝ)..r, g x)-f r‖ ≤ ε*R := by
  have hi : (f 0+∫ x in (0 : ℝ)..r, g x)-f r=
      ∫ x in (0 : ℝ)..r, (g x-deriv f x) := by
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable 0 r)
      (hf.continuous_deriv_one.intervalIntegrable 0 r),
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => (hf.differentiable one_ne_zero x).hasDerivAt)
        (hf.continuous_deriv_one.intervalIntegrable 0 r)]
    abel
  rw [hi]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)).trans
    (show ε*|r-0| ≤ ε*R by rw [sub_zero,abs_of_nonneg hr.1]; exact mul_le_mul_of_nonneg_left hr.2 hε)
  rw [uIoc_of_le hr.1] at hx
  exact he x ⟨hx.1.le,hx.2.trans hr.2⟩

theorem spectralContinuous_smoothApprox (f : ℝ → ℂ) (hf : Continuous f)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ ∀ r ∈ Icc 0 R, ‖g r-f r‖ ≤ ε := by
  let φ : ContDiffBump (0 : ℝ) :=
    { rIn := R+1
      rOut := R+2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let ψ : ℝ → ℂ := fun x => (φ x : ℂ)
  have hψ : Continuous ψ := Complex.continuous_ofReal.comp φ.continuous
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  let F : ℝ → ℂ := fun x => ψ x*f x
  have hFc : Continuous F := hψ.mul hf
  have hFs : HasCompactSupport F := hψc.mul_right
  obtain ⟨g,hg,he⟩ := (hFs.uniformContinuous_of_continuous hFc).exists_contDiff_dist_le hε
  refine ⟨g,hg,fun r hr => ?_⟩
  have hφ : φ r=1 := by
    apply φ.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hr.1]
      using (show r ≤ φ.rIn by change r ≤ R+1; linarith [hr.2])
  simpa only [dist_eq_norm,F,ψ,hφ,Complex.ofReal_one,one_mul] using (he r).le

theorem spectralSmooth_schwartzLocalize (P : ℝ → ℂ) (hP : ContDiff ℝ ∞ P)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ S : 𝓢(ℝ,ℂ), ∀ r ∈ Icc 0 R, S r=P r ∧ deriv S r=deriv P r := by
  let φ : ContDiffBump (0 : ℝ) :=
    { rIn := R+1
      rOut := R+2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let ψ : ℝ → ℂ := fun x => (φ x : ℂ)
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp φ.contDiff
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  let S : 𝓢(ℝ,ℂ) := (hψc.mul_right (f' := P)).toSchwartzMap (hψ.mul hP)
  refine ⟨S,fun r hr => ?_⟩
  have hb : r ∈ Metric.ball (0 : ℝ) φ.rIn := by
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hr.1]
      using (show r < φ.rIn by change r < R+1; linarith [hr.2])
  have he : (S : ℝ → ℂ) =ᶠ[𝓝 r] P := by
    filter_upwards [φ.eventuallyEq_one_of_mem_ball hb] with t ht
    change (φ t : ℂ)*P t=P t
    simp only [ht,Pi.one_apply,Complex.ofReal_one,one_mul]
  exact ⟨he.self_of_nhds,he.deriv_eq⟩

theorem spectralC1SchwartzApprox (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ S : 𝓢(ℝ,ℂ), ∀ r ∈ Icc 0 R,
      ‖S r-f r‖ ≤ ε*R ∧ ‖deriv S r-deriv f r‖ ≤ ε := by
  obtain ⟨g,hg,he⟩ := spectralContinuous_smoothApprox (deriv f) hf.continuous_deriv_one R ε hR hε
  let P := fun r => f 0+∫ x in (0 : ℝ)..r, g x
  obtain ⟨hP,hPd⟩ := spectralSmoothPrimitive (f 0) g hg
  obtain ⟨S,hS⟩ := spectralSmooth_schwartzLocalize P hP R hR
  refine ⟨S,fun r hr => ⟨?_,?_⟩⟩
  · rw [(hS r hr).1]
    exact spectralPrimitiveApprox_bound f g hf hg.continuous R ε hε.le he r hr
  · rw [(hS r hr).2,hPd r]
    exact he r hr

end DefocusingNLS

end OAI
