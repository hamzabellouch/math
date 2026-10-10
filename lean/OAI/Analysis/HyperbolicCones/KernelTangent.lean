import OAI.Analysis.HyperbolicCones.KernelSmooth
import OAI.Analysis.HyperbolicCones.TangentBasic

namespace OAI

noncomputable section

open scoped ContDiff Topology RealInnerProductSpace Matrix.Norms.L2Operator
open Set Filter

namespace Paper256

theorem kernel_projection_tangent_derivative (c : ℕ) (hC : 0 < c)
    (E : Sym 4 →ₗ[ℝ] Sym c) :
    ∃ (v : Vec 4) (T : Vec 4 →ₗ[ℝ] Mat c ℝ),
      ‖v‖ = 1 ∧ v 0 ≠ 0 ∧ ∀ h : Vec 4, inner ℝ v h = 0 →
        HasDerivAt (fun s : ℝ => kernelProjection
          (E (1 - outerSym (tangentCurve v h s)) : Mat c ℝ)) (T h) 0 := by
  obtain ⟨v, U, F, hv, hv0, hU, hvU, hF, heq⟩ :=
    kernel_projection_smooth_local_extension c hC E
  have hd : DifferentiableAt ℝ F v :=
    (hF.contDiffAt (hU.mem_nhds hvU)).differentiableAt (by norm_num)
  refine ⟨v, (fderiv ℝ F v).toLinearMap, hv, hv0, ?_⟩
  intro h hh
  have hc := tangentCurve_derivative v h
  have hcomp : HasDerivAt (fun s => F (tangentCurve v h s)) ((fderiv ℝ F v) h) 0 := by
    simpa only [Function.comp_apply] using!
      hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by simp [tangentCurve])
  apply hcomp.congr_of_eventuallyEq
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), tangentCurve v h s ∈ U := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa [tangentCurve] using hU.mem_nhds hvU
  filter_upwards [hmem] with s hs
  exact (heq _ hs (tangentCurve_unit v h hv hh s)).symm

end Paper256

end

end OAI
