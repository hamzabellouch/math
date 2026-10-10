import OAI.Analysis.IrrationalRotation.Model.ProductSampling

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel

def prefixEndpoint (D : ℕ) (x y : Base) : Base :=
  selectedEndpoint (Finset.range D) x y

def prefixPair (D : ℕ) (xy : EndpointPair) : EndpointPair :=
  (xy.1, prefixEndpoint D xy.1 xy.2)

def prefixPairLaw (ν : Measure EndpointPair) (D : ℕ) : Measure EndpointPair :=
  ν.map (prefixPair D)

end Invariant233.ProductModel

end

end OAI
