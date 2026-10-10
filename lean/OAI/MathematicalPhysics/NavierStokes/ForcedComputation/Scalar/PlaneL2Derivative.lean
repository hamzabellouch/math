import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneL2Continuity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneStrongDerivative

namespace OAI

/-! Strong differentiation of the scalar in the actual L2 norm. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set Filter
open scoped Topology

theorem planeL2_slope_ae (U : ℝ → PlaneL2) {F : ℝ → Plane → ℝ}
    {s t : ℝ}
    (hs : (fun x => U s x) =ᵐ[volume] F s)
    (ht : (fun x => U t x) =ᵐ[volume] F t) :
    (fun x => slope U t s x) =ᵐ[volume]
      fun x => slope (fun r => F r x) t s := by
  rw [slope_def_module]
  have he := (Lp.coeFn_smul (s - t)⁻¹ (U s - U t)).trans
    (((Lp.coeFn_sub (U s) (U t)).trans (hs.sub ht)).const_smul (s - t)⁻¹)
  filter_upwards [he] with x hx
  simpa only [slope_def_module, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using hx

theorem planeL2_hasDerivWithinAt_of_strongDerivative
    {F G : ℝ → Plane → ℝ} {S : Set ℝ} {U V : ℝ → PlaneL2}
    (hU : ∀ t ∈ S, (fun x => U t x) =ᵐ[volume] F t)
    (hV : ∀ t ∈ S, (fun x => V t x) =ᵐ[volume] G t)
    (hF : PlaneStrongDerivativeOn F G S) {t : ℝ} (ht : t ∈ S) :
    HasDerivWithinAt U (V t) S t := by
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : Tendsto (fun s => ‖slope U t s - V t‖ ^ 2)
      (𝓝[S \ {t}] t) (𝓝 (0 : ℝ)) := by
    apply (tendsto_congr' ?_).mpr (hF t ht)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact planeL2_sub_norm_sq (slope U t s) (V t)
      (planeL2_slope_ae U (hU s hs.1) (hU t ht)) (hV t ht)
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hroot

end ForcedComputation.VelocityDetector

end

end OAI
