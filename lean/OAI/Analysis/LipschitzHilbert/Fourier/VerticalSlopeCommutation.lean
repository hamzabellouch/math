import OAI.Analysis.LipschitzHilbert.Fourier.VerticalSamplingCommutator
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalConvolutionL1

namespace OAI

/-! Exact commutation of the vertical convolution and the frozen-direction
time integral. These identities precede all norm estimates. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalConvolution_sampled_measurable (K : ℝ → ℂ) (hKm : Measurable K)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) :
    Measurable (fun p : ℝ×(ℝ×ℝ) => verticalConvolution K (sampledFunction u p.1 f) p.2) := by
  have hm : Measurable (fun p : (ℝ×(ℝ×ℝ))×ℝ =>
      K p.2*f (p.1.2.1-p.1.1,p.1.2.2-p.2-p.1.1*u (p.1.2.1,p.1.2.2-p.2))) := by
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem verticalConvolution_slopeKernelOperator (K T : ℝ → ℂ)
    (hK : Integrable K) (hT : Integrable T)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    Integrable (fun t => T t*verticalConvolution K (sampledFunction u t f) z) ∧
      verticalConvolution K (slopeKernelOperator T u f) z=
        ∫ t, T t*verticalConvolution K (sampledFunction u t f) z := by
  let H := fun p : ℝ×ℝ => (K p.1*T p.2)*
    f (z.1-p.2,z.2-p.1-p.2*u (z.1,z.2-p.1))
  have hH : Integrable H (volume.prod volume) := by
    apply (hK.mul_prod hT).mul_bdd (c:=SchwartzMap.seminorm ℝ 0 0 f)
    · exact (f.continuous.measurable.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun p => SchwartzMap.norm_le_seminorm ℝ f _
  have hleft (s : ℝ) : K s*slopeKernelOperator T u f (z.1,z.2-s)=∫ t, H (s,t) := by
    rw [slopeKernelOperator,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [H]
    ring
  have hright (t : ℝ) : (∫ s, H (s,t))=T t*verticalConvolution K (sampledFunction u t f) z := by
    rw [verticalConvolution,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with s
    dsimp only [H,sampledFunction]
    ring
  refine ⟨?_,?_⟩
  · simpa only [hright] using hH.integral_prod_right
  · change (∫ s, K s*slopeKernelOperator T u f (z.1,z.2-s))=_
    simp_rw [hleft]
    rw [integral_integral_swap hH]
    simp_rw [hright]

theorem verticalSlopeCommutator_eq (K T : ℝ → ℂ)
    (hKm : Measurable K) (hK : Integrable K) (hT : Integrable T)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    verticalConvolution K (slopeKernelOperator T u f) z-
      slopeKernelOperator T u (verticalConvolution K f) z=
        ∫ t, T t*verticalSamplingCommutator K u t f z := by
  obtain ⟨hi1,heq⟩ := verticalConvolution_slopeKernelOperator K T hK hT u hum f z
  have hqm := verticalConvolution_measurable K hKm f f.continuous.measurable
  have hi2 : Integrable (fun t => T t*sampledFunction u t (verticalConvolution K f) z) := by
    apply (hT.norm.mul_const ((SchwartzMap.seminorm ℝ 0 0 f)*(∫ s, ‖K s‖))).mono'
    · exact hT.aestronglyMeasurable.mul (hqm.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with t
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (verticalConvolution_uniform_bound K hK f
        (SchwartzMap.seminorm ℝ 0 0 f) (SchwartzMap.norm_le_seminorm ℝ f) _) (norm_nonneg _)
  rw [heq]
  change (∫ t, T t*verticalConvolution K (sampledFunction u t f) z)-
    (∫ t, T t*sampledFunction u t (verticalConvolution K f) z)=_
  rw [←integral_sub hi1 hi2]
  apply integral_congr_ae
  filter_upwards [] with t
  exact (mul_sub _ _ _).symm

end LipschitzHilbert.PacketRepresentation

end

end OAI
