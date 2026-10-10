import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveStripPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveStripFourierSeparation

namespace OAI

/-! The actual normalized residue equals the explicit arithmetic model
on every positive-height strip. The remaining normalization scalar is retained. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaPositiveModelIdentity {ε : ℝ} (hε : 0<ε) :
    cubicThetaPositiveCuspRestriction hε cubicThetaNormalizedArithmeticResidue=
      cubicThetaPositiveModelStrip cubicThetaArithmeticBaseScalar hε := by
  apply sub_eq_zero.mp
  apply cubicThetaPositiveStripFourier_separates hε
  intro h W hW hsm
  rw [inner_sub_right,cubicThetaPositiveModelStrip_observations hε h W hW hsm,sub_self]

end CubicFirstMoment

end

end OAI
