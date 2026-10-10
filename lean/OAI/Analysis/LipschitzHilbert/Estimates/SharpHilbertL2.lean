import OAI.Analysis.LipschitzHilbert.Estimates.HilbertFiniteL2
import OAI.Analysis.LipschitzHilbert.Estimates.HilbertArbitraryEndpoint
import OAI.Analysis.LipschitzHilbert.Estimates.PublishedHilbertInput
import OAI.Analysis.LipschitzHilbert.Estimates.SharpTimeMoment

namespace OAI

/-! A uniform L2 estimate for all finite sharp one-dimensional Hilbert
truncations. This is a proved foundation for the remaining Lp input. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

private theorem energy_eLpNorm_bound (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (f : SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0≤C)
    (he : (∫ x, ‖g x‖^2)≤C^2*(∫ x, ‖f x‖^2)) :
    eLpNorm g 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  have hout := memLp_toL2_norm_sq volume g hg
  have hin := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  change ‖f.toLp 2 volume‖^2=_ at hin
  rw [←hout,←hin] at he
  have hn : ‖hg.toLp g‖≤C*‖f.toLp 2 volume‖ :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
      (by simpa only [mul_pow] using he)
  rw [←Lp.enorm_toLp hg,←ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn

theorem sharpHilbert_uniform_L2 : ∃ C : ℝ, 0<C ∧
    ∀ r R : ℝ, 0<r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      MemLp (oneDimensionalTruncatedHilbert r R f) 2 volume ∧
      eLpNorm (oneDimensionalTruncatedHilbert r R f) 2 volume≤
        ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_arbitrary_endpoint
  refine ⟨B+Real.pi,by linarith [Real.pi_pos],?_⟩
  intro r R hr hrR f
  have hR : 0<R := hr.trans_le hrR
  have hhalf : 0<R/2 := by positivity
  obtain ⟨N,_,_,hEi,hEb⟩ := hkernel r R hr hrR
  let K := sharpTimeKernel r R
  let J := finiteTimeKernel hilbertTimeKernel N (R/2)
  let E := fun t => K t-J t
  have hKi : Integrable K := sharpTimeKernel_integrable r R hr (hr.trans_le hrR)
  have hJi : Integrable J := finiteTimeKernel_integrable _ N (R/2) hhalf
  have hEm : Measurable E := (sharpTimeKernel_measurable r R).sub
    (finiteTimeKernel_measurable _ N (R/2))
  have herror := lineConvolution_energy_bound E hEi hEm f f.continuous.measurable (f.memLp 2 volume)
  have hEb' : (∫ t, ‖E t‖)^2≤B^2 := pow_le_pow_left₀
    (integral_nonneg fun _ => norm_nonneg _) hEb 2
  have herrorBound := energy_eLpNorm_bound (lineConvolution E f) herror.1 f B hB
    (herror.2.trans (mul_le_mul_of_nonneg_right hEb' (integral_nonneg fun _ => sq_nonneg _)))
  have hsmooth := hilbertFinite_L2 N (R/2) hhalf f
  have hsmoothBound := energy_eLpNorm_bound (lineConvolution J f) hsmooth.1 f Real.pi
    Real.pi_pos.le hsmooth.2
  have heq : oneDimensionalTruncatedHilbert r R f=lineConvolution E f+lineConvolution J f := by
    funext x
    have hsub : lineConvolution E f x=lineConvolution K f x-lineConvolution J f x := by
      change (∫ t, (K t-J t)*f (x-t))=_
      simp_rw [sub_mul]
      exact integral_sub
        (lineConvolution_integrand_of_bounded K f hKi f.continuous.measurable
          (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x)
        (lineConvolution_integrand_of_bounded J f hJi f.continuous.measurable
          (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x)
    change lineConvolution K f x=_
    rw [Pi.add_apply,hsub,sub_add_cancel]
  rw [heq]
  refine ⟨herror.1.add hsmooth.1,?_⟩
  calc
    _ ≤ eLpNorm (lineConvolution E f) 2 volume+eLpNorm (lineConvolution J f) 2 volume :=
      eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (B*‖f.toLp 2 volume‖)+ENNReal.ofReal (Real.pi*‖f.toLp 2 volume‖) :=
      add_le_add herrorBound hsmoothBound
    _ = _ := by
      rw [←ENNReal.ofReal_add (mul_nonneg hB (norm_nonneg _))
        (mul_nonneg Real.pi_pos.le (norm_nonneg _))]
      congr 1
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
