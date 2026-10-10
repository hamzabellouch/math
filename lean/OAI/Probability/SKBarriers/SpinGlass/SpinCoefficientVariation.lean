import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinTerminalDerivative
import OAI.Probability.SKBarriers.SpinGlass.SpinCovarianceVariation

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinPressure_coefficient_variation {N : ℕ} (d : ℕ)
    (I : Fin d → Finset (Fin N)) (a : Fin d → ℝ) (m : Fin d → ℝ) (i : Fin d) :
    fderiv ℝ (fun a : Fin d → ℝ =>
      hierarchyPressure d m (affineLogPartition (fun _ => 0) (spinExponent d a I)) 0) a
      (Pi.single i 1) =
      a i*(1-∑ j : Fin (d+1), if i.val < j.val then hierarchyAtom d m 1 j *
        (∫ z, (hierarchySpinMean d m (spinExponent d a I) (fun s => spinMonomial s (I i)) j z)^2
          ∂hierarchyPathLaw d m (affineLogPartition (fun _ => 0) (spinExponent d a I)) 0) else 0) := by
  rw [spinPressure_parameterDerivative_single]
  apply hierarchyGaussian_coordinate_spin d m (spinExponent d a I) (fun s => spinMonomial s (I i)) (a i) i
  · intro s
    simp only [spinExponent,coordinateLinear_coordinateAxis]
  · intro s
    rw [Real.norm_eq_abs]
    exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith [spinMonomial_sq s (I i)])
  · intro s
    exact spinMonomial_sq s (I i)
end SK.Analytic

end
end

end

end OAI
