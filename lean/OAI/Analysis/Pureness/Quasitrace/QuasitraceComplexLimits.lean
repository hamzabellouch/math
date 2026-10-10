import OAI.Analysis.Pureness.Quasitrace.QuasitraceSelfAdjointLimits
import OAI.Analysis.Pureness.Quasitrace.QuasitracePartsCauchy

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace UniformSpace Filter
open scoped Topology NNReal ComplexStarModule
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))
include hadd hsqrt

lemma complex_values_converge (u : ℕ → D) (hu : T.IsMetricCauchy u)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ k, ‖u k‖ ≤ C) :
    ∃ v : ℂ, Tendsto (fun k => T.complexValue (u k)) atTop (nhds v) := by
  obtain ⟨a,ha⟩ := T.selfAdjoint_values_converge hadd hsqrt (fun k => ℜ (u k))
    (T.isMetricCauchy_realPart hadd hu) C hC (fun k => (realPart.norm_le _).trans (hb k))
  obtain ⟨b,hb⟩ := T.selfAdjoint_values_converge hadd hsqrt (fun k => ℑ (u k))
    (T.isMetricCauchy_imaginaryPart hadd hu) C hC (fun k => (imaginaryPart.norm_le _).trans (hb k))
  refine ⟨(a:ℂ)+Complex.I*(b:ℂ),?_⟩
  exact (Complex.continuous_ofReal.tendsto a |>.comp ha).add
    ((Complex.continuous_ofReal.tendsto b |>.comp hb).const_mul Complex.I)

lemma selfAdjoint_values_same_limit (u v : ℕ → selfAdjoint D)
    (hu : T.IsMetricCauchy (fun k => (u k).1))
    (hv : T.IsMetricCauchy (fun k => (v k).1))
    (huv : T.IsMetricNull (fun k => (u k).1-(v k).1))
    (C : ℝ) (hC : 0 ≤ C) (hbu : ∀ k, ‖(u k).1‖ ≤ C) (hbv : ∀ k, ‖(v k).1‖ ≤ C)
    (a b : ℝ) (ha : Tendsto (fun k => T.selfAdjointValue (u k)) atTop (nhds a))
    (hb : Tendsto (fun k => T.selfAdjointValue (v k)) atTop (nhds b)) : a = b := by
  let p (k : ℕ) : Positive D := ⟨(u k).1+C • 1,selfAdjoint_add_bound_nonneg (u k) C (hbu k)⟩
  let q (k : ℕ) : Positive D := ⟨(v k).1+C • 1,selfAdjoint_add_bound_nonneg (v k) C (hbv k)⟩
  have hp := T.isMetricCauchy_add hadd hu (T.isMetricCauchy_const (C • (1:D)))
  have hq := T.isMetricCauchy_add hadd hv (T.isMetricCauchy_const (C • (1:D)))
  have hn : T.IsMetricNull (fun k => (p k).1-(q k).1) := by
    simpa only [p,q,add_sub_add_right_eq_sub] using huv
  have hep (k : ℕ) : T (p k) = T.selfAdjointValue (u k)+C*T ⟨1,zero_le_one⟩ := by
    have h := T.selfAdjointValue_shift (u k) C hC (hbu k)
    change T.selfAdjointValue (u k) = T (p k)-_ at h
    linarith
  have heq (k : ℕ) : T (q k) = T.selfAdjointValue (v k)+C*T ⟨1,zero_le_one⟩ := by
    have h := T.selfAdjointValue_shift (v k) C hC (hbv k)
    change T.selfAdjointValue (v k) = T (q k)-_ at h
    linarith
  have he := T.positive_values_same_limit hadd hsqrt p q hp hq hn
    (a+C*T ⟨1,zero_le_one⟩) (b+C*T ⟨1,zero_le_one⟩)
    (by simpa only [hep] using ha.add_const (C*T ⟨1,zero_le_one⟩))
    (by simpa only [heq] using hb.add_const (C*T ⟨1,zero_le_one⟩))
  linarith

lemma complex_values_same_limit (u v : ℕ → D) (hu : T.IsMetricCauchy u) (hv : T.IsMetricCauchy v)
    (huv : T.IsMetricNull (fun k => u k-v k))
    (C : ℝ) (hC : 0 ≤ C) (hbu : ∀ k, ‖u k‖ ≤ C) (hbv : ∀ k, ‖v k‖ ≤ C)
    (a b : ℂ) (ha : Tendsto (fun k => T.complexValue (u k)) atTop (nhds a))
    (hb : Tendsto (fun k => T.complexValue (v k)) atTop (nhds b)) : a = b := by
  have har : Tendsto (fun k => T.selfAdjointValue (ℜ (u k))) atTop (nhds a.re) := by
    simpa [Function.comp_def,complexValue] using (Complex.continuous_re.tendsto a).comp ha
  have hbr : Tendsto (fun k => T.selfAdjointValue (ℜ (v k))) atTop (nhds b.re) := by
    simpa [Function.comp_def,complexValue] using (Complex.continuous_re.tendsto b).comp hb
  have hai : Tendsto (fun k => T.selfAdjointValue (ℑ (u k))) atTop (nhds a.im) := by
    simpa [Function.comp_def,complexValue] using (Complex.continuous_im.tendsto a).comp ha
  have hbi : Tendsto (fun k => T.selfAdjointValue (ℑ (v k))) atTop (nhds b.im) := by
    simpa [Function.comp_def,complexValue] using (Complex.continuous_im.tendsto b).comp hb
  have hnr : T.IsMetricNull (fun k => (ℜ (u k) : D)-(ℜ (v k) : D)) := by
    simpa [map_sub] using T.isMetricNull_realPart hadd huv
  have hni : T.IsMetricNull (fun k => (ℑ (u k) : D)-(ℑ (v k) : D)) := by
    simpa [map_sub] using T.isMetricNull_imaginaryPart hadd huv
  exact Complex.ext
    (T.selfAdjoint_values_same_limit hadd hsqrt _ _ (T.isMetricCauchy_realPart hadd hu)
      (T.isMetricCauchy_realPart hadd hv) hnr C hC
      (fun k => (realPart.norm_le _).trans (hbu k)) (fun k => (realPart.norm_le _).trans (hbv k))
      a.re b.re har hbr)
    (T.selfAdjoint_values_same_limit hadd hsqrt _ _ (T.isMetricCauchy_imaginaryPart hadd hu)
      (T.isMetricCauchy_imaginaryPart hadd hv) hni C hC
      (fun k => (imaginaryPart.norm_le _).trans (hbu k)) (fun k => (imaginaryPart.norm_le _).trans (hbv k))
      a.im b.im hai hbi)
end CuntzPureness.PositiveQuasitrace

end

end OAI
