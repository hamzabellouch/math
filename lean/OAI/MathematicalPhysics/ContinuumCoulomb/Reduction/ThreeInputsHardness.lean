import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.RemainingInputsHardness
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalOscillatorGap

namespace OAI

/-!
Continuum Coulomb hardness under the planar spectral, flow and
finite-spin hardness hypotheses.
-/

noncomputable section
namespace ContinuumCoulomb

theorem unit_coulomb_qmaHard_of_three_inputs
    (hcmp : PublishedCMPHardness)
    (hp : PlanarSobolev.PublishedNegativePlanarGroundGap)
    (hflow : PublishedC4FlowInput) :
    QMAHard unitCoulombCodec.encode unitCoulombPromise :=
  unit_coulomb_qmaHard_of_remaining_inputs hcmp hp publishedVerticalOscillatorGap hflow

theorem binary_coulomb_qmaHard_of_three_inputs
    (hcmp : PublishedCMPHardness)
    (hp : PlanarSobolev.PublishedNegativePlanarGroundGap)
    (hflow : PublishedC4FlowInput) :
    QMAHard binaryCoulombCodec.encode binaryCoulombPromise :=
  binary_coulomb_qmaHard_of_remaining_inputs hcmp hp publishedVerticalOscillatorGap hflow

end ContinuumCoulomb

end

end OAI
