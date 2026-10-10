import OAI.Probability.InvariantIsing.Cavity.CavityGaussianJointTest
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

namespace OAI

/-! The measurable Gaussian kernel used by finite cavity marks. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

def cavityGaussianKernel {a L : Type*} [Fintype a] [DecidableEq a]
    [MeasurableSpace L] : Kernel (L × Matrix a a ℝ) (EuclideanSpace ℝ a) where
  toFun p := multivariateGaussian 0 p.2
  measurable' := measurable_multivariateGaussian.comp
    (measurable_const.prodMk measurable_snd)

instance {a L : Type*} [Fintype a] [DecidableEq a] [MeasurableSpace L] :
    IsMarkovKernel (cavityGaussianKernel (a := a) (L := L)) where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ a) p.2)
    infer_instance

end InvariantIsing

end

end OAI
