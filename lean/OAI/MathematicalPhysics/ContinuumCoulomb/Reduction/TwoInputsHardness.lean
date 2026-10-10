import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.ThreeInputsHardness
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarGroundUniqueness

namespace OAI

/-!
Continuum Coulomb hardness under the flow and finite-spin hardness
hypotheses.
-/

noncomputable section
namespace ContinuumCoulomb

theorem unit_coulomb_qmaHard_of_two_inputs
    (hcmp : PublishedCMPHardness) (hflow : PublishedC4FlowInput) :
    QMAHard unitCoulombCodec.encode unitCoulombPromise := by
  obtain ⟨s,_hs,hsource⟩ := hcmp
  obtain ⟨reduction⟩ := exists_source_unit_reduction_with_planar_gap hflow
    PlanarSobolev.manufacturedPlanarWell_gap_proved publishedVerticalOscillatorGap
    publishedSobolevSmoothDensity s
  exact hsource.of_reduction reduction

theorem binary_coulomb_qmaHard_of_two_inputs
    (hcmp : PublishedCMPHardness) (hflow : PublishedC4FlowInput) :
    QMAHard binaryCoulombCodec.encode binaryCoulombPromise :=
  UnitBinaryProgram.binary_hard_of_unit (unit_coulomb_qmaHard_of_two_inputs hcmp hflow)

end ContinuumCoulomb

end

end OAI
