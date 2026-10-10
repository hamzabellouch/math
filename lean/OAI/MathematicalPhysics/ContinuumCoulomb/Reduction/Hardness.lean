import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceHardness
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.OneInputHardness

namespace OAI

/-!
QMA hardness of continuum Coulomb energy with unit nuclear charges
and with binary-encoded positive integer nuclear charges.
-/

noncomputable section
namespace ContinuumCoulomb

theorem unit_coulomb_qmaHard : QMAHard unitCoulombCodec.encode unitCoulombPromise :=
  unit_coulomb_qmaHard_of_cmp publishedCMPHardness

theorem binary_coulomb_qmaHard : QMAHard binaryCoulombCodec.encode binaryCoulombPromise :=
  binary_coulomb_qmaHard_of_cmp publishedCMPHardness

end ContinuumCoulomb

end

end OAI
