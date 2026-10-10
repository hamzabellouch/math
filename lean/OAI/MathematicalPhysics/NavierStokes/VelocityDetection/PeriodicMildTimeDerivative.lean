import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicMildPeriodicData
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicTime

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicMild.PeriodicData
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ZeroAtInfty BigOperators
open PeriodicSpace.Jets

def timeDerivative (d : PeriodicData) : PeriodicData where
  scalar t X := JointCalculus.dAlong (1,0) (uncurry d.scalar) (t,X)
  smooth := by
    convert JointCalculus.contDiff_dAlong (1,0) d.smooth using 1
    rfl
  periodic := by
    intro t X Y hXY
    have hd (Z : Coord 2) : HasDerivAt (fun s => d.scalar s Z)
        (JointCalculus.dAlong (1,0) (uncurry d.scalar) (t,Z)) t := by
      simpa only [comp_def, id_eq, uncurry_apply_pair, JointCalculus.dAlong] using
        (d.smooth.differentiable (by simp) (t,Z)).hasFDerivAt.comp_hasDerivAt t
          ((hasDerivAt_id t).prodMk (hasDerivAt_const t Z))
    dsimp only
    rw [← (hd X).deriv, ← (hd Y).deriv]
    congr 1
    funext r
    exact d.periodic r hXY

theorem hasDerivAt_scalar (d : PeriodicData) (t : ℝ) (X : Coord 2) :
    HasDerivAt (fun s => d.scalar s X) (d.timeDerivative.scalar t X) t := by
  have hh := (d.smooth.differentiable (by simp) (t,X)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t X))
  simpa only [comp_def, id_eq, uncurry_apply_pair, timeDerivative, JointCalculus.dAlong] using hh

theorem hasDerivAt_jets (d : PeriodicData) (a : ℕ) (t : ℝ) :
    HasDerivAt (d.jets a) (d.timeDerivative.jets a t) t := by
  apply hasDerivAt_of_evaluations (d.timeDerivative.continuous_jets a)
  intro r X
  simpa only [jets_value] using d.hasDerivAt_scalar r X

theorem contDiff_jets_nat (k : ℕ) (d : PeriodicData) (a : ℕ) :
    ContDiff ℝ k (d.jets a) := by
  induction k generalizing d with
  | zero => exact contDiff_zero.mpr (d.continuous_jets a)
  | succ k ih =>
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun t => (1 : ℝ →L[ℝ] ℝ).smulRight (d.timeDerivative.jets a t), ?_, ?_⟩
    · exact (ContinuousLinearMap.smulRightL ℝ ℝ (E a) 1).contDiff.comp (ih d.timeDerivative)
    · intro t
      exact (d.hasDerivAt_jets a t).hasFDerivAt

theorem contDiff_jets (d : PeriodicData) (a : ℕ) : ContDiff ℝ ∞ (d.jets a) :=
  contDiff_infty.mpr (fun k => contDiff_jets_nat k d a)

end VelocityDetection.PeriodicMild.PeriodicData
end

end OAI
