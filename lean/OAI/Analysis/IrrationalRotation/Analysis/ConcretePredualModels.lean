import OAI.Analysis.IrrationalRotation.Analysis.ConcretePredualComplete
import OAI.Analysis.IrrationalRotation.Rotation.RotationHilbert
import OAI.Analysis.IrrationalRotation.Product.ProductHilbert

namespace OAI

noncomputable section
namespace Invariant233

theorem Rotation.algebra_hasSeparablePredual (θ : ℝ) :
    HasSeparablePredual (Rotation.algebra θ) :=
  ConcretePredual.hasSeparablePredual _

theorem ProductModel.factor_hasSeparablePredual (θ : ℕ → ℝ) :
    HasSeparablePredual (ProductModel.factor θ) :=
  ConcretePredual.hasSeparablePredual _

end Invariant233

end

end OAI
