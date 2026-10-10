import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.TwoInputsHardness
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowUniform

namespace OAI

/-!
Continuum Coulomb hardness follows from hardness of the field-free
signed square-lattice Heisenberg energy problem.
-/

noncomputable section
namespace ContinuumCoulomb

theorem unit_coulomb_qmaHard_of_cmp (hcmp : PublishedCMPHardness) :
    QMAHard unitCoulombCodec.encode unitCoulombPromise :=
  unit_coulomb_qmaHard_of_two_inputs hcmp publishedC4FlowInput

theorem binary_coulomb_qmaHard_of_cmp (hcmp : PublishedCMPHardness) :
    QMAHard binaryCoulombCodec.encode binaryCoulombPromise :=
  binary_coulomb_qmaHard_of_two_inputs hcmp publishedC4FlowInput

end ContinuumCoulomb

end

end OAI
