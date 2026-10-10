import OAI.Analysis.IrrationalRotation.Rotation.RotationDiffuse
import OAI.Analysis.IrrationalRotation.Analysis.ConcretePredualModels

namespace OAI

noncomputable section
namespace Invariant233.Rotation

theorem factor_structure (θ : ℝ) (hθ : Irrational θ) :
    IsTypeII1FactorWithVector (algebra θ) vacuum ∧
      HasSeparablePredual (algebra θ) :=
  ⟨algebra_isTypeII1FactorWithVector θ hθ, algebra_hasSeparablePredual θ⟩

end Invariant233.Rotation

end

end OAI
