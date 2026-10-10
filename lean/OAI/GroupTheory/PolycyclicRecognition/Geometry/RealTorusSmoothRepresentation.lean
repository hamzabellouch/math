import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealTorusContinuity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealNormedLieAlgebra
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AutomaticSmoothAlgebraHom

namespace OAI

/-! # Smoothness of the rotational representation along a Lie group character -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- The compact rotations as units of the continuous endomorphism algebra. -/
def realTorusUnitAction : realRotationTorus L H →* (L →L[ℝ] L)ˣ where
  toFun z := (realTorusAutomorphism L H z).toLinearEquiv.toContinuousLinearEquiv.toUnit
  map_one' := by
    apply Units.ext
    apply ContinuousLinearMap.ext
    intro x
    exact realTorusOperator_one L H x
  map_mul' z w := by
    apply Units.ext
    apply ContinuousLinearMap.ext
    intro x
    exact realTorusOperator_mul L H z w x

theorem realTorusUnitAction_apply (z : realRotationTorus L H) (x : L) :
    (realTorusUnitAction H z : L →L[ℝ] L) x = realTorusOperator L H z x := rfl

theorem continuous_realTorusUnitAction :
    Continuous (fun z : realRotationTorus L H => (realTorusUnitAction H z : L →L[ℝ] L)) := by
  apply continuous_clm_apply.mpr
  intro x
  change Continuous (fun z : realRotationTorus L H => realTorusOperator L H z x)
  have ha : Continuous (fun p : realRotationTorus L H × L =>
      realTorusOperator L H p.1 p.2) := continuous_realTorusOperator L H
  have hp : Continuous (fun z : realRotationTorus L H => (z,x)) :=
    continuous_id.prodMk continuous_const
  simpa only [Function.comp_def] using
    (Continuous.comp (f := fun z : realRotationTorus L H => (z,x))
      (g := fun p : realRotationTorus L H × L => realTorusOperator L H p.1 p.2) ha hp)

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]

/-- A continuous compact rotation character of a Lie group has a smooth
linear representation. No manifold structure on the compact torus is needed. -/
theorem contMDiff_realTorusRepresentation
    {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G} (hExp : IsGroupExponential Exp)
    (q : G →* realRotationTorus L H) (hq : Continuous q) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,L →L[ℝ] L)) ∞
      (fun g => (realTorusUnitAction H (q g) : L →L[ℝ] L)) := by
  exact contMDiff_of_continuous_unitsHom hExp ((realTorusUnitAction H).comp q)
    ((continuous_realTorusUnitAction H).comp hq)

end PolycyclicRecognition

end

end OAI
