import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPeriodicProperties

namespace OAI

/-! Classical scalar advection-diffusion on the flat two-torus.

Mantegazza and Martinazzi, A note on quasilinear parabolic equations on
manifolds, Ann. Sc. Norm. Super. Pisa (5) 11 (2012), 857--874,
Proposition 2.3 and Remark 2.4 (p. 861), specialized to the flat two-torus,
second order, constant positive diffusion and a prescribed smooth drift.
Finite-time coefficients can be extended with a time cutoff before applying
the globally bounded-coefficient result.
-/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set
open scoped ContDiff

def scalarLaplacian (w : Plane → ℝ) (x : Plane) : ℝ :=
  ∑ j : Fin 2, spatialD j (spatialD j w) x

def scalarGenerator (ν : ℝ) (a : Plane → Plane) (w : Plane → ℝ) (x : Plane) : ℝ :=
  ν * scalarLaplacian w x - fderiv ℝ w x (a x)

/-- Smoothness and the actual scalar equation on a finite closed cylinder.
The time derivative is one-sided at its two endpoints. -/
structure TorusScalarSolution (T ν : ℝ) (a : ℝ → Plane → Plane)
    (h w : ℝ → Plane → ℝ) (w₀ : Plane → ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ (Function.uncurry w) (Icc 0 T ×ˢ univ)
  periodic : ∀ t ∈ Icc 0 T, PlanePeriodic (w t)
  initial : w 0 = w₀
  equation : ∀ t ∈ Icc 0 T, ∀ x,
    HasDerivWithinAt (fun s => w s x)
      (scalarGenerator ν (a t) (w t) x + h t x) (Icc 0 T) t

theorem TorusScalarSolution.slice_smooth {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hw : TorusScalarSolution T ν a h w w₀) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ ∞ (w t) := by
  have hi : ContDiff ℝ ∞ (fun x : Plane => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  have hh := hw.smooth.comp hi.contDiffOn
    (show MapsTo (fun x : Plane => (t, x)) univ (Icc 0 T ×ˢ univ) from
      fun x _ => ⟨ht, mem_univ x⟩)
  simpa only [Function.comp_def, Function.uncurry_apply_pair, contDiffOn_univ] using hh

/-- Classical existence for smooth periodic scalar advection-diffusion on a
finite time cylinder. -/
def TorusScalarExistence : Prop :=
  ∀ (T ν : ℝ), 0 < T → 0 < ν →
    ∀ (a : ℝ → Plane → Plane) (h : ℝ → Plane → ℝ) (w₀ : Plane → ℝ),
    ContDiff ℝ ∞ (Function.uncurry a) →
    ContDiff ℝ ∞ (Function.uncurry h) → ContDiff ℝ ∞ w₀ →
    (∀ t, PlanePeriodic (a t)) → (∀ t, PlanePeriodic (h t)) → PlanePeriodic w₀ →
    ∃ w, TorusScalarSolution T ν a h w w₀

theorem scalarLaplacian_zero (x : Plane) : scalarLaplacian (fun _ => 0) x = 0 := by
  have hd (j : Fin 2) : spatialD j (fun _ : Plane => (0 : ℝ)) = fun _ => 0 := by
    funext y
    simp [spatialD]
  simp only [scalarLaplacian, hd, Finset.sum_const_zero]

theorem scalarGenerator_zero (ν : ℝ) (a : Plane → Plane) (x : Plane) :
    scalarGenerator ν a (fun _ => 0) x = 0 := by
  simp [scalarGenerator, scalarLaplacian_zero]

theorem zero_solution (T ν : ℝ) (a : ℝ → Plane → Plane) :
    TorusScalarSolution T ν a (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) := by
  refine ⟨contDiffOn_const, fun _ _ _ _ => rfl, rfl, ?_⟩
  intro t _ x
  simpa only [scalarGenerator_zero, add_zero] using
    (hasDerivWithinAt_const t (Icc (0 : ℝ) T) (0 : ℝ))

end ForcedComputation.VelocityDetector

end

end OAI
