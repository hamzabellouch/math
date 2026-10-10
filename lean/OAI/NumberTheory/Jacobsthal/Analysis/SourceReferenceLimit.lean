import OAI.NumberTheory.Jacobsthal.Estimates.SourceParentBenchmark
import OAI.NumberTheory.Jacobsthal.Estimates.SourceReferenceRemainders

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceReferenceMargin
open ErdosCorrectionLimit ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.ReferenceSourceDecomposition NumberTheoryLean.ReferenceLocalResidual
open Erdos970Dependency.InvariantCostBound

theorem root_sourceReference_tendsto (a : ℝ) :
    Tendsto (fun z => (ErdosInverseBoxHeight.sourceB z)^2*
      sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode a z)) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant*(-a+2*signedCoefficientI/costMass))) := by
  have hh := (((root_source_remainder_tendsto a).add (root_anomaly_replacement_tendsto a)).add
    (root_nodeBenchmark_tendsto a)).add (floored_source_correction_tendsto a)
  convert! hh using 1
  · funext z
    ring
  · ring_nf

theorem actual_sourceReference_tendsto :
    Tendsto (fun z => (ErdosInverseBoxHeight.sourceB z)^2*
      sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z)) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant*(-(1:ℝ)/100+2*signedCoefficientI/costMass))) := by
  simpa only [neg_div] using! root_sourceReference_tendsto (1/100)

end ErdosSourceReferenceMargin

end

end Erdos970

end OAI
