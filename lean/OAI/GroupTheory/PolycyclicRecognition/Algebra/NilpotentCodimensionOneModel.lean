import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentSemidirectTangent
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentIdealNorm
import Mathlib.Analysis.Convex.Contractible

namespace OAI

/-! # Extending a polynomial ideal model by one dimension -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [LieRing.IsNilpotent L] (C : LieCodimensionOneData L)

def nilpotentModelOfPolynomialIdeal
    (P : letI := C.normedIdeal; PolynomialExponentialCoordinates C.ideal) :
    NilpotentLieModel L := by
  letI := C.normedIdeal
  letI := P
  let D := C.derivation
  have hD : IsNilpotent D.toLinearMap := C.derivation_nilpotent
  let normedV : NormedAddCommGroup (C.ideal × ℝ) := inferInstance
  letI : NormedAddCommGroup (C.ideal × ℝ) := normedV
  letI : AddCommGroup (C.ideal × ℝ) := normedV.toAddCommGroup
  letI : MetricSpace (C.ideal × ℝ) := normedV.toMetricSpace
  letI : UniformSpace (C.ideal × ℝ) :=
    normedV.toMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace (C.ideal × ℝ) :=
    normedV.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : ChartedSpace (C.ideal × ℝ) (C.ideal × ℝ) := chartedSpaceSelf _
  letI : T0Space (C.ideal × ℝ) := @MetricSpace.instT0Space _ normedV.toMetricSpace
  letI : T2Space (C.ideal × ℝ) := inferInstance
  letI : CompleteSpace (C.ideal × ℝ) := FiniteDimensional.complete ℝ (C.ideal × ℝ)
  letI : Group (C.ideal × ℝ) := derivationSemidirectGroup D hD
  letI : LieGroup (𝓘(ℝ, C.ideal × ℝ)) ⊤ (C.ideal × ℝ) := derivationSemidirectLieGroup D hD
  letI : LieRing (C.ideal × ℝ) :=
    inferInstanceAs (LieRing (GroupLieAlgebra (𝓘(ℝ, C.ideal × ℝ)) (C.ideal × ℝ)))
  letI : LieAlgebra ℝ (C.ideal × ℝ) :=
    inferInstanceAs (LieAlgebra ℝ (GroupLieAlgebra (𝓘(ℝ, C.ideal × ℝ)) (C.ideal × ℝ)))
  letI : MeasurableSpace (C.ideal × ℝ) := borel (C.ideal × ℝ)
  letI : BorelSpace (C.ideal × ℝ) := ⟨rfl⟩
  have hbr (x y : C.ideal) (s t : ℝ) :
      ⁅((x, s) : GroupLieAlgebra (𝓘(ℝ, C.ideal × ℝ)) (C.ideal × ℝ)),
        ((y, t) : GroupLieAlgebra (𝓘(ℝ, C.ideal × ℝ)) (C.ideal × ℝ))⁆ =
      (⁅x, y⁆ + s • D y - t • D x, 0) :=
    semidirect_tangent_bracket D hD (derivationSemidirect_one D hD)
      (derivationSemidirect_mul D hD) x y s t
  let e : GroupLieAlgebra (𝓘(ℝ, C.ideal × ℝ)) (C.ideal × ℝ) ≃ₗ⁅ℝ⁆ L :=
    { C.split with
      map_lie' := by
        intro x y
        let xp : C.ideal × ℝ := x
        let yp : C.ideal × ℝ := y
        have hh := hbr xp.1 yp.1 xp.2 yp.2
        exact (congrArg C.split hh).trans (C.split_lie xp.1 yp.1 xp.2 yp.2).symm }
  exact { modelSpace := C.ideal × ℝ, carrier := C.ideal × ℝ, equiv := e.symm }

end PolycyclicRecognition

end

end OAI
