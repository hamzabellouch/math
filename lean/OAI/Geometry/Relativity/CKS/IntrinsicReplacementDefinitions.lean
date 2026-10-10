import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.CutSurface

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory CKSLorentz CKSMetricGluing
open scoped ContDiff Topology ENNReal
namespace CKSIntrinsicConstraints
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

attribute [local instance] eight_atLeastTwo

end CKSIntrinsicConstraints

end

end OAI
