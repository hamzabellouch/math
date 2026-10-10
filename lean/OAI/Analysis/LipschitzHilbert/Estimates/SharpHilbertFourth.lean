import OAI.Analysis.LipschitzHilbert.Estimates.HilbertFiniteFourth
import OAI.Analysis.LipschitzHilbert.Estimates.HilbertArbitraryEndpoint
import OAI.Analysis.LipschitzHilbert.Estimates.PublishedHilbertInput
import OAI.Analysis.LipschitzHilbert.Estimates.SharpTimeMoment

namespace OAI

/-! A uniform fourth-power estimate for the actual sharp truncations. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem sharpHilbert_uniform_fourth : ∃ D : ℝ, 0≤D ∧
    ∀ r R : ℝ, 0<r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^4) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^4)≤D*(∫ x, ‖f x‖^4) := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_arbitrary_endpoint
  let D := 68*16*Real.pi^4*(∫ t, ‖(𝓕⁻ verticalBinPlateau : SchwartzMap ℝ ℂ) t‖)^4
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨8*(B^4+D),by positivity,?_⟩
  intro r R hr hrR f
  have hhalf : 0<R/2 := by linarith
  obtain ⟨N,_,_,hEi,hEb⟩ := hkernel r R hr hrR
  let K := sharpTimeKernel r R
  let J := finiteTimeKernel hilbertTimeKernel N (R/2)
  let E := fun t => K t-J t
  have hKi : Integrable K := sharpTimeKernel_integrable r R hr (hr.trans_le hrR)
  have hJi : Integrable J := finiteTimeKernel_integrable _ N (R/2) hhalf
  have hEm : Measurable E := (sharpTimeKernel_measurable r R).sub
    (finiteTimeKernel_measurable _ N (R/2))
  have he := lineConvolution_fourth_bound E hEi hEm f
  have hj := lineConvolution_fourth_bound J hJi (finiteTimeKernel_measurable _ _ _) f
  have heBound : (∫ x, ‖lineConvolution E f x‖^4)≤B^4*(∫ x, ‖f x‖^4) :=
    he.2.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (integral_nonneg fun _ => norm_nonneg _) hEb 4)
      (integral_nonneg fun _ => by positivity))
  have hjBound : (∫ x, ‖lineConvolution J f x‖^4)≤D*(∫ x, ‖f x‖^4) :=
    hilbertFinite_fourth N (R/2) hhalf f
  have heq (x : ℝ) : oneDimensionalTruncatedHilbert r R f x=
      lineConvolution E f x+lineConvolution J f x := by
    have hsub : lineConvolution E f x=lineConvolution K f x-lineConvolution J f x := by
      change (∫ t, (K t-J t)*f (x-t))=_
      simp_rw [sub_mul]
      exact integral_sub
        (lineConvolution_integrand_of_bounded K f hKi f.continuous.measurable
          (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x)
        (lineConvolution_integrand_of_bounded J f hJi f.continuous.measurable
          (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x)
    change lineConvolution K f x=_
    rw [hsub,sub_add_cancel]
  have hm : Measurable (oneDimensionalTruncatedHilbert r R f) :=
    lineConvolution_measurable K (sharpTimeKernel_measurable r R) f f.continuous.measurable
  have hd := (he.1.add hj.1).const_mul 8
  have hp (x : ℝ) : ‖oneDimensionalTruncatedHilbert r R f x‖^4≤
      8*(‖lineConvolution E f x‖^4+‖lineConvolution J f x‖^4) := by
    rw [heq]
    exact norm_add_fourth_le _ _
  have hi : Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^4) := by
    apply hd.mono' (hm.norm.pow_const 4).aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Pi.add_apply,Real.norm_of_nonneg (by positivity : 0≤‖oneDimensionalTruncatedHilbert r R f x‖^4)] using hp x
  refine ⟨hi,?_⟩
  have hh := integral_mono hi hd hp
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add he.1 hj.1] at hh
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
