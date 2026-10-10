import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarCharacteristics
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarMassEvolution

namespace OAI

/-! For the detector, preservation of the transported bump's mass follows
directly from its transport equation and periodic integration by parts. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory
open scoped ContDiff

theorem scalar_spatial_fderiv_smooth {u : ℝ → Plane → ℝ}
    (hu : ContDiff ℝ ∞ (Function.uncurry u)) :
    ContDiff ℝ ∞ (fun y : ℝ × Plane => fderiv ℝ (u y.1) y.2) := by
  have h : ContDiff ℝ ∞
      (Function.uncurry (fun y : ℝ × Plane => fun x : Plane => u y.1 x)) :=
    hu.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact h.fderiv contDiff_snd (by simp)

theorem pullbackScalar_mass {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hV : ContDiff ℝ ∞ (Function.uncurry V))
    (hp : ∀ s, PlanePeriodic (V s))
    (hdiv : ∀ s x, PlanarHamiltonian.divergence (V s) x = 0)
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
    {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (hgp : PlanePeriodic g) (t : ℝ) :
    (∫ x in Icc (0 : Plane) (fun _ => 1), pullbackScalar Ψ g t x) =
      ∫ x in Icc (0 : Plane) (fun _ => 1), g x := by
  let u := pullbackScalar Ψ g
  let d : ℝ → Plane → ℝ := fun s x => -fderiv ℝ (u s) x (V s x)
  have hu : ContDiff ℝ ∞ (Function.uncurry u) := hg.comp hback
  have hd : Continuous (Function.uncurry d) :=
    ((scalar_spatial_fderiv_smooth hu).clm_apply hV).neg.continuous
  have hVs : ∀ s, ContDiff ℝ ∞ (V s) :=
    fun s => hV.comp (contDiff_const.prodMk contDiff_id)
  have hm (s : ℝ) : HasDerivAt (scalarMass u) 0 s := by
    have h := scalarMass_source_derivative (ν := 0) (h := fun _ _ => 0) hu hd
      hVs hp
      (pullbackScalar_periodic hΨ hp hgp) hdiv
      (pullbackScalar_transport hΨ hback hg)
      (fun s x => by simp only [d, scalarGenerator, zero_mul, zero_sub, add_zero])
      (fun _ => continuous_const) s
    simpa only [scalarMass, integral_zero] using h
  have he : scalarMass u t = scalarMass u 0 :=
    is_const_of_deriv_eq_zero (fun s => (hm s).differentiableAt)
      (fun s => (hm s).deriv) t 0
  change scalarMass u t = _
  rw [he]
  simp only [scalarMass, u, pullbackScalar, neg_zero, hΨ.initial]

end ForcedComputation.VelocityDetector

end

end OAI
