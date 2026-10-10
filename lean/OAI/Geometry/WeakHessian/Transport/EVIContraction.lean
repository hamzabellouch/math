import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.EVICalculus

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile72
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology

lemma evi_doubling_contraction {D : ℝ → ℝ → ℝ} {E F : ℝ → ℝ} {K b : ℝ}
    (hE : Continuous E) (hF : Continuous F) (hb : 0 ≤ b)
    (hDc : ContinuousOn (fun t => D t t) (Icc 0 b))
    (h1 : ∀ x h r : ℝ,0 ≤ x → 0 ≤ h → 0 ≤ r →
      (Real.exp (K*h)*D (x+h) r-D x r)/2 ≤
      ∫ s in 0..h,Real.exp (K*s)*(F r-E (x+s)))
    (h2 : ∀ x h r : ℝ,0 ≤ x → 0 ≤ h → 0 ≤ r →
      (Real.exp (K*h)*D r (x+h)-D r x)/2 ≤
      ∫ s in 0..h,Real.exp (K*s)*(E r-F (x+s))) :
    Real.exp (2*K*b)*D b b ≤ D 0 0 := by
  let g : ℝ → ℝ := fun t => Real.exp (2*K*t)*D t t
  have hgc : ContinuousOn g (Icc 0 b) := (by fun_prop : ContinuousOn (fun t : ℝ => Real.exp (2*K*t)) (Icc 0 b)).mul hDc
  apply image_le_of_liminf_slope_right_le_deriv_boundary (f := g) (B := fun _ => D 0 0) (B' := fun _ => 0) hgc
    (by simp [g]) continuousOn_const (fun x _ => (hasDerivAt_const x (D 0 0)).hasDerivWithinAt) _ ⟨hb,le_rfl⟩
  intro x hx r hr
  have hsub : Tendsto (fun z : ℝ => z-x) (𝓝[>] x) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [sub_self] using ((by fun_prop : Continuous (fun z : ℝ => z-x)).tendsto x).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_pos.mpr (show x < z from hz)
  have hR := (evi_error_ratio_tendsto hE hF K x).comp hsub
  apply Filter.Eventually.frequently
  filter_upwards [hR.eventually_lt_const hr,self_mem_nhdsWithin] with z hz hxz
  have hh : 0 < z-x := sub_pos.mpr hxz
  have H := evi_rectangle (h1 x (z-x) (x+(z-x)) hx.1 hh.le (add_nonneg hx.1 hh.le))
    (h2 x (z-x) x hx.1 hh.le hx.1) hh
  rw [slope_def_field]
  have Hg : (g z-g x)/(z-x) ≤ 2*Real.exp (2*K*x)*
      (Real.exp (K*(z-x))*((∫ s in 0..z-x,Real.exp (K*s)*(F (x+(z-x))-E (x+s)))/(z-x))+
        (∫ s in 0..z-x,Real.exp (K*s)*(E x-F (x+s)))/(z-x)) := by
    simpa only [g,add_sub_cancel] using H
  exact Hg.trans_lt hz
end WeakHessian

end
end InlinedFile72

end OAI
