import OAI.Analysis.CircleDomains.Sobolev.CurveCoareaInput
import OAI.Analysis.CircleDomains.Sobolev.LipschitzFiberIntegralBound
import OAI.Analysis.CircleDomains.Probability.BorelFiberCounts

namespace OAI

/-! The published plane-to-line coarea input, with its exact finite-H1
Borel-set hypotheses. Both the completed measurability and the sharp
constant-one inequality are proved. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma planarLipschitzFiberCoarea : PlanarLipschitzFiberCoarea := by
  intro A hA hfin L f hf
  exact ⟨aemeasurable_hausdorff_zero_fiber hA hf.continuous volume,
    lipschitz_fiber_integral_le A hfin L f hf⟩

end CircleDomainRigidity

end

end OAI
