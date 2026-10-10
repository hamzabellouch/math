import OAI.Analysis.IrrationalRotation.Model.ProductSampling
import OAI.Analysis.IrrationalRotation.Analysis.L2UniformAbsoluteContinuity

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.ProductModel

theorem HasUniformL2Marginals.uniformlyAbsolutelyContinuous
    {η : ℕ → Measure EndpointPair} (hη : HasUniformL2Marginals η) :
    UniformlyAbsolutelyContinuous baseMeasure (fun l => (η l).map Prod.fst) ∧
    UniformlyAbsolutelyContinuous baseMeasure (fun l => (η l).map Prod.snd) := by
  rcases hη with ⟨H, _hH, hη⟩
  constructor
  · apply EndpointLoss.uniformlyAbsolutelyContinuous_of_Lp_densities baseMeasure _ H
    intro l
    rcases hη l with ⟨f, g, hf, _hg, hmf, _hmg, hbf, _hbg⟩
    exact ⟨f, hf, hmf, hbf⟩
  · apply EndpointLoss.uniformlyAbsolutelyContinuous_of_Lp_densities baseMeasure _ H
    intro l
    rcases hη l with ⟨f, g, _hf, hg, _hmf, hmg, _hbf, hbg⟩
    exact ⟨g, hg, hmg, hbg⟩

end Invariant233.ProductModel

end OAI
