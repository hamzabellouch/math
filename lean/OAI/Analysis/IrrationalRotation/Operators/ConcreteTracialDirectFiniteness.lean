import OAI.Analysis.IrrationalRotation.Operators.TracialDirectFiniteness
import OAI.Analysis.IrrationalRotation.Rotation.RotationTrace
import OAI.Analysis.IrrationalRotation.Product.ProductTracialVector

namespace OAI

noncomputable section

namespace Invariant233

theorem Rotation.algebra_isDedekindFiniteMonoid (θ : ℝ) :
    IsDedekindFiniteMonoid (Rotation.algebra θ) :=
  (Rotation.vacuum_faithfulTracial θ).isDedekindFiniteMonoid

theorem ProductModel.factor_isDedekindFiniteMonoid (θ : ℕ → ℝ) :
    IsDedekindFiniteMonoid (ProductModel.factor θ) :=
  (ProductModel.traceVector_faithfulTracial θ).isDedekindFiniteMonoid

end Invariant233

end

end OAI
