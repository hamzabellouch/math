import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealTorusSmoothRepresentation

namespace OAI

/-! # Compact rotations on the concrete model space of a Lie group -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)) [H.IsCartanSubalgebra]

/-- This version uses the original model-space norm and scalar structures. -/
def tangentTorusUnitAction :
    realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* (E →L[ℝ] E)ˣ where
  toFun z :=
    let e : E ≃ₗ[ℝ] E := (realTorusAutomorphism (GroupLieAlgebra (𝓘(ℝ,E)) G) H z).toLinearEquiv
    e.toContinuousLinearEquiv.toUnit
  map_one' := by
    apply Units.ext
    apply ContinuousLinearMap.ext
    intro x
    exact realTorusOperator_one (GroupLieAlgebra (𝓘(ℝ,E)) G) H x
  map_mul' z w := by
    apply Units.ext
    apply ContinuousLinearMap.ext
    intro x
    exact realTorusOperator_mul (GroupLieAlgebra (𝓘(ℝ,E)) G) H z w x

theorem continuous_tangentTorusUnitAction :
    Continuous (fun z => (tangentTorusUnitAction H z : E →L[ℝ] E)) := by
  apply continuous_clm_apply.mpr
  intro x
  have ha : Continuous (fun p : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H × E =>
      realTorusOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H p.1 p.2) :=
    continuous_realTorusOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H
  have hp : Continuous (fun z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H => (z,x)) :=
    continuous_id.prodMk continuous_const
  have hc : Continuous (fun z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H =>
      realTorusOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H z x) := by
    simpa only [Function.comp_def] using
      (Continuous.comp (f := fun z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H => (z,x))
        (g := fun p : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H × E =>
          realTorusOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H p.1 p.2) ha hp)
  exact (tangentSpaceCastModel (𝓘(ℝ,E)) (1 : G)).continuous.comp hc

theorem contMDiff_tangentTorusRepresentation
    {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G} (hExp : IsGroupExponential Exp)
    (q : G →* realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) (hq : Continuous q) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun g => (tangentTorusUnitAction H (q g) : E →L[ℝ] E)) := by
  exact contMDiff_of_continuous_unitsHom hExp ((tangentTorusUnitAction H).comp q)
    ((continuous_tangentTorusUnitAction H).comp hq)

end PolycyclicRecognition

end

end OAI
