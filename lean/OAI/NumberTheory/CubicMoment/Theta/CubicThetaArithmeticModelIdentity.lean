import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticModelObservation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaStripFourierSeparation

namespace OAI

/-! The actual normalized arithmetic residue equals its explicit
arithmetic coefficient series in the cusp L2 space. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaArithmeticModelIdentity :
    cubicThetaCuspRestriction cubicThetaNormalizedArithmeticResidue=
      cubicThetaArithmeticModelStrip cubicThetaArithmeticBaseScalar := by
  apply sub_eq_zero.mp
  apply cubicThetaStripFourier_separates
  intro h W hW
  rw [inner_sub_right,cubicThetaArithmeticModel_all_observations h W hW,sub_self]

end CubicFirstMoment

end

end OAI
