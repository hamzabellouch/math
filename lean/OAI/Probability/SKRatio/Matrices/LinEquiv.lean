import Mathlib
import OAI.Probability.SKRatio.Matrices.Lin

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKRatioGaussian.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def linEquiv : Matrix ι ι ℂ ≃ₗ[ℂ] (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap

def linHom : Matrix ι ι ℂ →+* (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) where
  toFun := lin
  map_one' := lin_one
  map_mul' := lin_mul
  map_zero' := linEquiv.map_zero
  map_add' := linEquiv.map_add

lemma continuous_lin : Continuous (lin : Matrix ι ι ℂ → _) :=
  (linEquiv (ι := ι)).toLinearMap.continuous_of_finiteDimensional

lemma lin_exp (M : Matrix ι ι ℂ) : lin (NormedSpace.exp M) = NormedSpace.exp (lin M) :=
  NormedSpace.map_exp linHom continuous_lin M

end SKRatioGaussian.ComplexMatrix

end
end
end
end
end
end
end
end
end

end OAI
