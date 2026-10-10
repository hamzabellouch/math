import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SubConst
import OAI.Geometry.WeakHessian.Transport.BoundedHopfMapLipschitz

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile87
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [IsFiniteMeasure m]

lemma continuousOn_integral_boundedHopfMap (f : X →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    ContinuousOn (fun s => ∫ x,boundedHopfMap f s x ∂m) (Ici 0) := by
  intro t ht
  have H := tendsto_bounded_pairing_L1 (m := m)
    (u := fun _ : ℝ => fun _ : X => (1:ℝ)) (v := fun _ : X => (1:ℝ))
    (fun _ => integrable_const _) (integrable_const _)
    (q := boundedHopfMap f) (r := boundedHopfMap f t)
    (continuousOn_boundedHopfMap hf t ht) (by simpa using (tendsto_const_nhds (x := (0:ℝ)) : Tendsto (fun _ : ℝ => (0:ℝ)) (𝓝[Ici 0] t) (𝓝 0)))
  change Tendsto _ _ _
  simpa using H

lemma integral_hopf_positive_slope (f : X →ᵇ ℝ) {t r : ℝ} (ht : 0 < t)
    (hr : -(∫ x,(localSlope (boundedHopfMap f t) x).toReal^2 ∂m)/2 < r) :
    ∀ᶠ s in 𝓝[>] t,slope (fun z => ∫ x,boundedHopfMap f z x ∂m) t s < r := by
  let D := ∫ x,(localSlope (boundedHopfMap f t) x).toReal^2 ∂m
  have hid : Tendsto (fun s : ℝ => s) (𝓝[>] t) (𝓝 t) := tendsto_id.mono_left nhdsWithin_le_nhds
  have Hlim : Tendsto (fun s : ℝ => -t/(2*s)*D) (𝓝[>] t) (𝓝 (-D/2)) := by
    convert ((tendsto_const_nhds (x := -t)).div (hid.const_mul 2) (by positivity : 2*t ≠ 0)).mul_const D using 1
    congr 1
    field_simp
  filter_upwards [Hlim.eventually_lt_const hr,self_mem_nhdsWithin] with s hs hst
  have H := boundedHopfMap_L1_increment (m := m) (fun _ _ => measure_lt_top _ _) f
    (u := fun _ : X => (1:ℝ)) (integrable_const _) (ae_of_all _ fun _ => zero_le_one) ht hst.le
  simp only [BoundedContinuousFunction.sub_apply,one_mul] at H
  rw [integral_sub ((boundedHopfMap f s).integrable (μ := m)) ((boundedHopfMap f t).integrable (μ := m))] at H
  rw [slope_def_field]
  apply lt_of_le_of_lt _ hs
  apply (div_le_iff₀ (sub_pos.mpr hst)).mpr
  convert! H using 1
  dsimp only [D]
  ring

lemma integral_hopf_falling (f : X →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    {a b : ℝ} (hb : 0 < b)
    (hE : ∀ t,0 < t → t < b → a ≤ (∫ x,(localSlope (boundedHopfMap f t) x).toReal^2 ∂m)/2) :
    (∫ x,boundedHopfMap f b x ∂m) ≤ (∫ x,f x ∂m)-a*b := by
  let J (t : ℝ) := ∫ x,boundedHopfMap f t x ∂m
  have hJ := continuousOn_integral_boundedHopfMap (m := m) f hf
  have H (c : ℝ) (hc : 0 < c) (hcb : c ≤ b) : J b ≤ J c-a*(b-c) := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary (f := J)
      (B := fun z => J c-a*(z-c)) (B' := fun _ => -a)
      (hJ.mono (fun _ hx => hc.le.trans hx.1)) (by simp) (by fun_prop)
      (fun x _ => by
        have hd := (((hasDerivAt_id x).sub_const c).const_mul a).const_sub (J c)
        convert! hd.hasDerivWithinAt (s := Ici x) using 1
        simp only [mul_one])
      _ ⟨hcb,le_rfl⟩
    intro x hx r hr
    exact (integral_hopf_positive_slope f (hc.trans_le hx.1)
      (lt_of_le_of_lt (by linarith [hE x (hc.trans_le hx.1) hx.2]) hr)).frequently
  have ht : Tendsto (fun c : ℝ => J c-a*(b-c)) (𝓝[>] 0) (𝓝 ((∫ x,f x ∂m)-a*b)) := by
    have hc := (hJ 0 (by simp)).mono (Ioi_subset_Ici_self (a := (0:ℝ)))
    have hid : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    change Tendsto J (𝓝[>] 0) (𝓝 (J 0)) at hc
    simpa only [J,boundedHopfMap_zero,sub_zero] using hc.sub (((tendsto_const_nhds (x := b)).sub hid).const_mul a)
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0)).eventually_lt_const hb)] with c hc hcb
  exact H c hc hcb.le
end WeakHessianTransport

end
end InlinedFile87

end OAI
