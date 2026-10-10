import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarTransition
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusScalarInput

namespace OAI

/-! The inviscid reference is constant along actual characteristics.
Its transport equation follows by differentiating that identity. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff

def pullbackScalar (Ψ : ℝ → ℝ → Plane → Plane) (g : Plane → ℝ)
    (t : ℝ) (x : Plane) : ℝ := g (Ψ t (-t) x)

theorem planar_transition_equivariant {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hp : ∀ s, PlanePeriodic (V s)) (a t : ℝ) (x : Plane) (k : Fin 2 → ℤ) :
    Ψ a t (x + fun j => (k j : ℝ)) = Ψ a t x + fun j => (k j : ℝ) := by
  symm
  apply hΨ.unique a (x + fun j => (k j : ℝ))
    (fun s => Ψ a s x + fun j => (k j : ℝ))
  · rw [hΨ.initial]
  · intro s
    rw [hp (a + s) (Ψ a s x) k]
    exact (hΨ.ode a s x).add_const (fun j => (k j : ℝ))

theorem pullbackScalar_periodic {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hp : ∀ s, PlanePeriodic (V s)) {g : Plane → ℝ} (hg : PlanePeriodic g) (t : ℝ) :
    PlanePeriodic (pullbackScalar Ψ g t) := by
  intro x k
  unfold pullbackScalar
  rw [planar_transition_equivariant hΨ hp, hg]

theorem pullbackScalar_along {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (g : Plane → ℝ) (t r : ℝ) (x : Plane) :
    pullbackScalar Ψ g (t + r) (Ψ t r x) = pullbackScalar Ψ g t x := by
  have he : Ψ 0 (t + r) (Ψ t (-t) x) = Ψ t r x := by
    rw [hΨ.compose 0 t r, zero_add]
    have hi : Ψ 0 t (Ψ t (-t) x) = x := by
      simpa only [zero_add] using hΨ.inverse_right 0 t x
    rw [hi]
  unfold pullbackScalar
  rw [← he]
  simpa only [zero_add] using congrArg g (hΨ.inverse_left 0 (t + r) (Ψ t (-t) x))

theorem scalar_characteristic_equation {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    {u : ℝ → Plane → ℝ} (hu : ContDiff ℝ ∞ (Function.uncurry u))
    (hinv : ∀ t r x, u (t + r) (Ψ t r x) = u t x) (t : ℝ) (x : Plane) :
    HasDerivAt (fun s => u s x) (-fderiv ℝ (u t) x (V t x)) t := by
  let D := fderiv ℝ (Function.uncurry u) (t, x)
  have hf : HasFDerivAt (Function.uncurry u) D (t, x) :=
    (hu.differentiable (by simp) (t, x)).hasFDerivAt
  have hγ : HasDerivAt (fun r => (t + r, Ψ t r x)) (1, V t x) 0 := by
    simpa only [add_zero, hΨ.initial, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).const_add t).prodMk (hΨ.ode t 0 x)
  have hfγ : HasFDerivAt (Function.uncurry u) D (t + 0, Ψ t 0 x) := by
    simpa only [add_zero, hΨ.initial] using hf
  have hc := hfγ.comp_hasDerivAt 0 hγ
  have hz : HasDerivAt (fun r => u (t + r) (Ψ t r x)) 0 0 := by
    simpa only [hinv] using hasDerivAt_const (0 : ℝ) (u t x)
  have he : D (1, V t x) = 0 := hc.unique hz
  have hspace := hf.comp x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  have hsp : D (0, V t x) = fderiv ℝ (u t) x (V t x) := by
    simpa only [Function.comp_def, Function.uncurry_apply_pair,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      zero_apply, ContinuousLinearMap.id_apply] using
      (congrArg (fun A : Plane →L[ℝ] ℝ => A (V t x)) hspace.fderiv).symm
  have hadd : ((1 : ℝ), V t x) = (1, (0 : Plane)) + (0, V t x) := by
    ext <;> simp
  rw [hadd, map_add, hsp] at he
  have htD : D (1, (0 : Plane)) = -fderiv ℝ (u t) x (V t x) := by linarith
  have htime := hf.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq, htD] using htime

theorem pullbackScalar_transport {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
    {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (t : ℝ) (x : Plane) :
    HasDerivAt (fun s => pullbackScalar Ψ g s x)
      (-fderiv ℝ (pullbackScalar Ψ g t) x (V t x)) t :=
  scalar_characteristic_equation (u := pullbackScalar Ψ g) hΨ (hg.comp hback)
    (pullbackScalar_along hΨ g) t x

end ForcedComputation.VelocityDetector

end

end OAI
