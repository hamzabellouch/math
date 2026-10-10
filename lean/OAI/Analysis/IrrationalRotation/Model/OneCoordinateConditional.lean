import OAI.Analysis.IrrationalRotation.Model.OneCoordinateCoupling
import OAI.Analysis.IrrationalRotation.Model.FiniteKernelMixture

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Invariant233.OneCoordinateCoupling
open CouplingMarginalBounds FiniteKernelMixture

noncomputable def rightGivenLeft (κ m a b t : ℝ) : Kernel ℝ ℝ :=
  diagonalReplacementKernel (ENNReal.ofReal (diagonalMass κ m a b t))
    (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
    (fun i x => ENNReal.ofReal (leftDensity m a b i x))
    (fun i => by fin_cases i <;>
      exact (measurable_const.indicator measurableSet_Ico).ennreal_ofReal)
    (rightLaw m a b)

noncomputable def leftGivenRight (κ m a b t : ℝ) : Kernel ℝ ℝ :=
  diagonalReplacementKernel (ENNReal.ofReal (diagonalMass κ m a b t))
    (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
    (fun i x => ENNReal.ofReal (rightDensity m a b i x))
    (fun i => by fin_cases i <;>
      exact (measurable_const.indicator measurableSet_Ico).ennreal_ofReal)
    (leftLaw m a b)

end Invariant233.OneCoordinateCoupling

end OAI
