import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneSquareContinuity
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! The square-distance formulation gives continuity in the usual L2
space, rather than only pointwise time continuity. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set Filter
open scoped Topology

abbrev PlaneL2 := Lp ℝ 2 (volume : Measure Plane)

theorem planeL2_norm_sq (u : PlaneL2) {f : Plane → ℝ}
    (hf : (fun x => u x) =ᵐ[volume] f) : ‖u‖ ^ 2 = ∫ x, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  change u x * u x = f x ^ 2
  rw [hx, pow_two]

theorem planeL2_sub_norm_sq (u v : PlaneL2) {f g : Plane → ℝ}
    (hf : (fun x => u x) =ᵐ[volume] f) (hg : (fun x => v x) =ᵐ[volume] g) :
    ‖u - v‖ ^ 2 = ∫ x, (f x - g x) ^ 2 := by
  apply planeL2_norm_sq
  exact (Lp.coeFn_sub u v).trans (hf.sub hg)

theorem planeL2_continuousOn_of_squareDistance {F : ℝ → Plane → ℝ}
    {S : Set ℝ} {U : ℝ → PlaneL2}
    (hU : ∀ t ∈ S, (fun x => U t x) =ᵐ[volume] F t)
    (hF : SquareDistanceContinuousOn F S) : ContinuousOn U S := by
  intro s hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : Tendsto (fun t => ‖U t - U s‖ ^ 2) (𝓝[S] s) (𝓝 (0 : ℝ)) := by
    apply (tendsto_congr' ?_).mpr (hF s hs)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact planeL2_sub_norm_sq (U t) (U s) (hU t ht) (hU s hs)
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hroot

end ForcedComputation.VelocityDetector

end

end OAI
