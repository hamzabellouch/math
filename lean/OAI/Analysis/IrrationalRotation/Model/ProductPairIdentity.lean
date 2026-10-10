import OAI.Analysis.IrrationalRotation.Model.ProductFactorStructure
import OAI.Analysis.IrrationalRotation.Model.ProductCocycle
import OAI.Analysis.IrrationalRotation.Model.ProductSampling
import OAI.Analysis.IrrationalRotation.Model.UnrestrictedDiagonal

namespace OAI

noncomputable section
namespace Invariant233.ProductModel

def cocycleRatio (θ c : ℕ → ℝ) (x y : Base) (k : ℤ) : ℝ :=
  ProductCocycle.cocycleVersion θ c k y / ProductCocycle.cocycleVersion θ c k x

def ratioDiagonal (θ c : ℕ → ℝ) (x y : Base) : Fiber →L[ℂ] Fiber :=
  SequenceHilbert.boundedDiagonal (fun k => (cocycleRatio θ c x y k : ℂ))

def PairIdentity (θ c : ℕ → ℝ) (F : Base → Fiber →L[ℂ] Fiber)
    (xy : EndpointPair) : Prop :=
  (∀ k : ℤ, 0 < cocycleRatio θ c xy.1 xy.2 k ∧
    cocycleRatio θ c xy.1 xy.2 k ≤ 1) ∧
  (1 - F xy.2) * ratioDiagonal θ c xy.1 xy.2 * F xy.1 = 0

end Invariant233.ProductModel

end

end OAI
