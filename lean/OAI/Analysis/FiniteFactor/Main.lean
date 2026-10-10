import OAI.Analysis.FiniteFactor.CrossedProduct.InvariantProjection
import OAI.Analysis.FiniteFactor.CrossedProduct.PreparedFactor

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem main_theorem : MainTarget.{0} := by
  obtain ⟨θ,hr,hphase,hs,_he,hcenter,hfinite,hminimal,hpredual,hθ,hT,hT0,_hinj,_hcontract,hqn⟩ :=
    exists_source_prepared_factor
  refine ⟨SourceHilbert SourceCoordinate,inferInstance,inferInstance,inferInstance,sourceAlgebra θ,
    hcenter,hfinite,hminimal,hpredual,
    sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg,hT,hT0,hqn,?_⟩
  intro p hp hproj hinv
  exact sourceInvariantProjection_trivial θ hθ hr hs hphase hp hproj hinv

end
end FiniteFactor

end OAI
