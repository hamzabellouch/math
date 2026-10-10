import OAI.Dynamics.StandardMap.LimitActions

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open TopologicalSpace Topology
namespace StandardMapEntropy
instance : PseudoMetrizableSpace DistanceArray := by
  let : PseudoMetrizableSpace (DyadicTime → DyadicTime → ℝ) := inferInstance
  exact PseudoMetrizableSpace.subtype _
instance : SecondCountableTopology DistanceArray := by
  let : SecondCountableTopology (DyadicTime → DyadicTime → ℝ) := inferInstance
  exact Subtype.secondCountableTopology _
instance : PseudoMetrizableSpace NonAffineArray := PseudoMetrizableSpace.subtype _
instance : SecondCountableTopology NonAffineArray := Subtype.secondCountableTopology _
instance : SigmaCompactSpace NonAffineArray := inferInstance
end StandardMapEntropy

end OAI
