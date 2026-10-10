import Mathlib
import OAI.Probability.SKBarriers.Scalar.PrefixAlgebra

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section SpinProduct
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem hierarchySpinMean_terminal_product (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hc : ∀ s, ‖c s‖ ≤ C) (j : Fin (n+1)) :
    (∫ sz, c sz.1*hierarchySpinMean n m U c j sz.2 ∂hierarchyGaussianLaw n m U) =
      ∫ z, (hierarchySpinMean n m U c j z)^2
        ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  let f := affineLogPartition (fun _ => 0) U
  have hf := affineLogPartition_boundedDerivs (fun _ => 0) U
  have hr := hierarchySpinMean_regular n m U c hC hc j
  rw [hierarchyGaussian_terminal_marginal n m U c _ hr.1 (HasExpGrowth.of_bounded hC hr.2)]
  have he : hierarchyMomentLevel n m f (hierarchySpinMean n m U c j) j =
      hierarchySpinMean n m U c j := hierarchyMomentLevel_retained n m f _ hf j j le_rfl
  have H := hierarchyPathLaw_fixed_mul n m f (affineMoment (fun _ => 0) U c)
    (hierarchySpinMean n m U c j) hf (affineMoment_continuous _ _ _) hr.1 hC hC
    (affineMoment_norm_le _ _ _ hc) hr.2 j he 0
  calc
    _ = ∫ z, hierarchySpinMean n m U c j z*affineMoment (fun _ => 0) U c z
        ∂hierarchyPathLaw n m f 0 := by congr 1; funext z; ring
    _ = _ := H.trans (by congr 1; funext z; change hierarchySpinMean n m U c j z * hierarchySpinMean n m U c j z = _; ring)

end SpinProduct
end SK.Analytic

end
end

end

end OAI
