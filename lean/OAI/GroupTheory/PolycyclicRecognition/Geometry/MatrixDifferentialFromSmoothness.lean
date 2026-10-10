import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraHomLieDifferential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularLieDifferential

namespace OAI

/-! # Discharging the matrix Lie differential input

The representation is only assumed continuous. Automatic smoothness is
proved using exponential product coordinates, and the Lie-homomorphism law
is proved using related vector fields in a chart.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

local instance matrixDifferentialChartedSpace (n : ℕ) :
    @ChartedSpace (Matrix (Fin n) (Fin n) ℝ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
        (@SeminormedAddCommGroup.toPseudoMetricSpace _
          (@NormedAddCommGroup.toSeminormedAddCommGroup _
            (Matrix.linftyOpNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ))))))
      (Matrix (Fin n) (Fin n) ℝ) inferInstance := by
  convert chartedSpaceSelf (Matrix (Fin n) (Fin n) ℝ) using 1
  rfl

theorem matrixLieDifferentialInput : MatrixLieDifferentialInput := by
  intro S n ρ hc _hi
  have hv : Continuous (fun g => (ρ g : Matrix (Fin n) (Fin n) ℝ)) :=
    Units.continuous_val.comp hc
  have hs : ContMDiff (𝓘(ℝ, S.modelSpace)) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ∞
      (fun g => (ρ g : Matrix (Fin n) (Fin n) ℝ)) :=
    contMDiff_of_continuous_unitsHom groupExponential_isGroupExponential ρ hv
  exact ⟨unitsHomLieDifferential ρ hs, hasMFDerivAt_unitsHomLieDifferential ρ hs⟩

end PolycyclicRecognition

end

end OAI
