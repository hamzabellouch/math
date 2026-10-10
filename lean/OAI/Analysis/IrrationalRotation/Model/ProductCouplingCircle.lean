import OAI.Analysis.IrrationalRotation.Model.ProductCoupling
import OAI.Analysis.IrrationalRotation.Model.ProductBase

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.OrderedProductCoupling

def circleEndpoint (x : Endpoint) : ProductModel.Base := fun i => (x i : Circle)

def realEndpoint (x : ProductModel.Base) : Endpoint :=
  fun i => circleRepresentative (x i)

def circleLeftEndpoint : Sample → ProductModel.Base := circleEndpoint ∘ leftEndpoint

def circleRightEndpoint : Sample → ProductModel.Base := circleEndpoint ∘ rightEndpoint

def circleHybridEndpoint (ε : ℕ → Bool) : Sample → ProductModel.Base :=
  circleEndpoint ∘ hybridEndpoint ε

def circlePairLaw (P : Parameters) : Measure (ProductModel.Base × ProductModel.Base) :=
  (law P).map (fun ω => (circleLeftEndpoint ω, circleRightEndpoint ω))

end Invariant233.OrderedProductCoupling

end

end OAI
