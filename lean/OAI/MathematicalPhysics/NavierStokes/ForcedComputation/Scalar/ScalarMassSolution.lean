import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarMassEvolution
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularFluid

namespace OAI

/-! The mass identity at every nonnegative time of a smooth global scalar
solution. Only the equation at that time is needed. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory
open scoped ContDiff

def scalarTimeDerivative (w : ℝ → Plane → ℝ) (t : ℝ) (x : Plane) : ℝ :=
  fderiv ℝ (Function.uncurry w) (t, x) (1, 0)

theorem scalarTimeDerivative_smooth {w : ℝ → Plane → ℝ}
    (hw : ContDiff ℝ ∞ (Function.uncurry w)) :
    ContDiff ℝ ∞ (Function.uncurry (scalarTimeDerivative w)) :=
  (hw.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem scalarTimeDerivative_hasDerivAt {w : ℝ → Plane → ℝ}
    (hw : ContDiff ℝ ∞ (Function.uncurry w)) (t : ℝ) (x : Plane) :
    HasDerivAt (fun s => w s x) (scalarTimeDerivative w t x) t := by
  exact ((hw.differentiable (by simp) (t, x)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

theorem GlobalTorusScalarSolution.mass_hasDerivAt {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hs : GlobalTorusScalarSolution ν a h w w₀)
    (hw : ContDiff ℝ ∞ (Function.uncurry w))
    (ha : ∀ t, ContDiff ℝ ∞ (a t))
    (hpa : ∀ t, PlanePeriodic (a t))
    (hdiv : ∀ t x, PlanarHamiltonian.divergence (a t) x = 0)
    (hh : ∀ t, Continuous (h t)) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (scalarMass w) (scalarMass h t) t := by
  have hd := scalarMass_hasDerivAt hw.continuous
    (scalarTimeDerivative_smooth hw).continuous (scalarTimeDerivative_hasDerivAt hw) t
  have he (x : Plane) : scalarTimeDerivative w t x =
      scalarGenerator ν (a t) (w t) x + h t x := by
    rw [← (scalarTimeDerivative_hasDerivAt hw t x).deriv]
    exact hs.deriv_eq hw ht x
  have hws : ContDiff ℝ ∞ (w t) := hw.comp (contDiff_const.prodMk contDiff_id)
  have hG : Continuous (fun x => scalarGenerator ν (a t) (w t) x) := by
    apply Continuous.sub
    · apply Continuous.const_mul
      apply continuous_finsetSum
      intro j _
      exact (PlanarHamiltonian.spatialD_smooth j
        (PlanarHamiltonian.spatialD_smooth j hws)).continuous
    · exact ((hws.fderiv_right (m := ∞) (by simp)).clm_apply (ha t)).continuous
  have hi : scalarMass (scalarTimeDerivative w) t = scalarMass h t := by
    unfold scalarMass
    simp_rw [he]
    rw [integral_add hG.integrableOn_Icc (hh t).integrableOn_Icc,
      scalarGenerator_integral_zero (ha t) hws (hpa t)
        ((hs t ht).periodic t ⟨ht, le_rfl⟩) (hdiv t) ν, zero_add]
  exact hi ▸ hd

end ForcedComputation.VelocityDetector

end

end OAI
