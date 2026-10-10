import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorMain
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarVariationDischarge
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCoefficientBounds
import Mathlib.Algebra.Field.Periodic

namespace OAI

/-! Smooth dependence for an arbitrary smooth periodic processor input.
The compact-detector input is not restricted to finite Hamiltonian expressions. -/

noncomputable section
namespace ForcedComputation

open Set ShearFlows
open scoped ContDiff NNReal

private theorem periodic_joint_bound {F : Type*} [NormedAddCommGroup F]
    {f : ℝ × Plane → F} (hc : Continuous f)
    (hp : ∀ t, PlanePeriodic (fun x => f (t,x)))
    (ht : ∀ x, Function.Periodic (fun t => f (t,x)) 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, ‖f (t,x)‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := planePeriodic_bound_on hc.continuousOn
    (fun t _ => hp t) (a := 0) (b := 1)
  refine ⟨C,hC,?_⟩
  intro t x
  have he : f (t,x) = f (Int.fract t,x) := by
    have h := (ht x).int_mul (⌊t⌋ : ℤ) (Int.fract t)
    simpa only [mul_one, Int.fract_add_floor] using h
  rw [he]
  exact hb (Int.fract t) ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩ x

namespace VelocityDetector.CompactCenter.ProcessorInput

/-- Time periodicity passes to the total space-time derivative. -/
theorem derivative_time_periodic {V : ℝ → Plane → Plane} (hV : ProcessorInput V)
    (x : Plane) : Function.Periodic (fun t => fderiv ℝ (Function.uncurry V) (t,x)) 1 := by
  have ht : ∀ p : ℝ × Plane, Function.uncurry V (p+(1,0)) = Function.uncurry V p := by
    rintro ⟨t,y⟩
    change V (t+1) (y+0) = V t y
    simpa only [add_zero] using hV.time_periodic t y
  intro t
  have hd := fderiv_translation (hV.smooth.differentiable (by simp)) ht (t,x)
  simpa only [Prod.mk_add_mk, add_zero] using hd

/-- Smooth periodicity supplies the qualitative joint derivative bound needed for the flow. -/
theorem joint_derivative_bound {V : ℝ → Plane → Plane} (hV : ProcessorInput V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, ‖fderiv ℝ (Function.uncurry V) p‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := periodic_joint_bound
    (hV.smooth.continuous_fderiv (by simp))
    (planePeriodic_totalDerivative hV.smooth hV.spatial_periodic)
    hV.derivative_time_periodic
  exact ⟨C,hC,fun p => hb p.1 p.2⟩

theorem joint_lipschitz {V : ℝ → Plane → Plane} (hV : ProcessorInput V) :
    ∃ L : ℝ≥0, LipschitzWith L (Function.uncurry V) := by
  obtain ⟨C,hC,hb⟩ := hV.joint_derivative_bound
  refine ⟨⟨C,hC⟩, lipschitzWith_of_nnnorm_fderiv_le (hV.smooth.differentiable (by simp)) ?_⟩
  intro p
  exact_mod_cast hb p

/-- Every actual transition of the supplied processor is jointly smooth. -/
theorem transition_joint_smooth {V : ℝ → Plane → Plane} (hV : ProcessorInput V)
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × Plane) => Ψ p.1 p.2.1 p.2.2) := by
  obtain ⟨L,hL⟩ := hV.joint_lipschitz
  exact Flow.transition_contDiff ⟨Function.uncurry V,hV.smooth.continuous⟩
    hV.smooth hL hΨ.ode hΨ.initial

/-- The first and second variational equations are consequences of the input data. -/
theorem variations {V : ℝ → Plane → Plane} (hV : ProcessorInput V)
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ) : PlanarVariations V Ψ :=
  variations_of_joint_smooth V Ψ hV.smooth (hV.transition_joint_smooth hΨ) hΨ

/-- The backward map used by the detector has the same joint smoothness. -/
theorem backward_smooth {V : ℝ → Plane → Plane} (hV : ProcessorInput V)
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ) :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => Ψ p.1 (-p.1) p.2) :=
  (hV.transition_joint_smooth hΨ).comp
    (contDiff_fst.prodMk (contDiff_fst.neg.prodMk contDiff_snd))

end VelocityDetector.CompactCenter.ProcessorInput
end ForcedComputation

end

end OAI
