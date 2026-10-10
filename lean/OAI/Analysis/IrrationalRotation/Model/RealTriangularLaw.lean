import OAI.Analysis.IrrationalRotation.Model.ProductCouplingCircle
import OAI.Analysis.IrrationalRotation.Model.ProductSampling

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.OrderedProductCoupling

def realSelectedEndpoint (I : Finset ℕ) (x z : Endpoint) : Endpoint :=
  fun i => if i ∈ I then z i else x i

def realTriangularEvent (I : Finset ℕ) : Set (Endpoint × Endpoint) :=
  {xz | ∀ i ∈ I, xz.1 i < xz.2 i}

def realTriangularLaw (I : Finset ℕ) : Measure (Endpoint × Endpoint) :=
  ((baseMeasure.prod baseMeasure).restrict (realTriangularEvent I)).map
    (fun xz => (xz.1, realSelectedEndpoint I xz.1 xz.2))

def circlePairEndpoint : Endpoint × Endpoint → ProductModel.EndpointPair :=
  Prod.map circleEndpoint circleEndpoint

end Invariant233.OrderedProductCoupling

end

end OAI
