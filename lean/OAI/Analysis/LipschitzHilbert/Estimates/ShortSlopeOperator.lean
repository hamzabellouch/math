import OAI.Analysis.LipschitzHilbert.Fourier.KernelAverageEnergy
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalSamplingGeometry

namespace OAI

/-! The short-time frozen-direction operator and the exact reason it may
replace the full kernel in a pairing on a narrow horizontal strip. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def shortSlopeOperator (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ)
    (z : ℝ×ℝ) : ℂ :=
  ∫ t, if |t|≤1/4 then K t*f (z.1-t,z.2-t*u z) else 0

theorem shortSlopeOperator_measurable (K : ℝ → ℂ) (hKm : Measurable K)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) :
    Measurable (shortSlopeOperator K u f) := by
  have hs : MeasurableSet {p : (ℝ×ℝ)×ℝ | |p.2|≤1/4} := by
    have hc : Continuous (fun p : (ℝ×ℝ)×ℝ => |p.2|) := by fun_prop
    exact (isClosed_le hc continuous_const).measurableSet
  have hm : Measurable (fun p : (ℝ×ℝ)×ℝ =>
      K p.2*f (p.1.1-p.2,p.1.2-p.2*u p.1)) := by fun_prop
  exact (hm.ite hs measurable_const).stronglyMeasurable.integral_prod_right'.measurable

theorem shortSlopeOperator_energy (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) :
    MemLp (shortSlopeOperator K u f) 2 planeMeasure ∧
      (∫ z, ‖shortSlopeOperator K u f z‖^2 ∂planeMeasure)≤
        4*(∫ t, ‖K t‖)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  let F := fun p : ℝ×(ℝ×ℝ) =>
    if |p.1|≤1/4 then f (p.2.1-p.1,p.2.2-p.1*u p.2) else 0
  have hum := hu.continuous.measurable
  have hs : MeasurableSet {p : ℝ×(ℝ×ℝ) | |p.1|≤1/4} := by
    have hc : Continuous (fun p : ℝ×(ℝ×ℝ) => |p.1|) := by fun_prop
    exact (isClosed_le hc continuous_const).measurableSet
  have hFm : Measurable F := (hfm.comp (by fun_prop)).ite hs measurable_const
  have henergy (t : ℝ) : MemLp (fun z => F (t,z)) 2 planeMeasure ∧
      (∫ z, ‖F (t,z)‖^2 ∂planeMeasure)≤4*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
    by_cases ht : |t|≤1/4
    · simpa only [F,ite_eq_left ht,Function.comp_def,verticalSampling,sub_zero] using
        verticalSampling_energy u hu t t 0 ht f hfm hf
    · simp only [F,ite_eq_right ht,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
      exact ⟨MemLp.zero',by positivity⟩
  have h := kernelAverage_energy K hKm hK F hFm (4*∫ z, ‖f z‖^2 ∂planeMeasure)
    (by positivity) (fun t => (henergy t).1) (fun t => (henergy t).2)
  have heq (z : ℝ×ℝ) : (∫ t, K t*F (t,z))=shortSlopeOperator K u f z := by
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [F]
    split_ifs <;> simp
  simp only [heq] at h
  refine ⟨h.1,h.2.trans_eq ?_⟩
  ring

theorem shortSlopeOperator_pairing_eq (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f g : (ℝ×ℝ) → ℂ) (l r : ℝ) (hwidth : r-l≤1/4)
    (hf : ∀ z, z.1∉Icc l r → f z=0) (hg : ∀ z, z.1∉Icc l r → g z=0)
    (z : ℝ×ℝ) :
    shortSlopeOperator K u f z*star (g z)=slopeKernelOperator K u f z*star (g z) := by
  by_cases hg0 : g z=0
  · simp only [hg0,star_zero,mul_zero]
  have hz : z.1∈Icc l r := by
    by_contra h
    exact hg0 (hg z h)
  unfold shortSlopeOperator slopeKernelOperator
  rw [←integral_mul_const,←integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : |t|≤1/4
  · simp only [ite_eq_left ht]
  · have hnot : z.1-t∉Icc l r := by
      intro h
      apply ht
      apply abs_le.mpr
      constructor <;> linarith [hz.1,hz.2,h.1,h.2]
    rw [ite_eq_right ht,hf _ hnot]
    simp only [mul_zero,zero_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
