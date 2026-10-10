import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.ConditionalHardness
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SobolevDensity

namespace OAI

/-!
Continuum Coulomb hardness under the planar spectral, vertical
spectral, flow and finite-spin hardness hypotheses.
-/

noncomputable section
namespace ContinuumCoulomb

theorem unit_coulomb_qmaHard_of_remaining_inputs
    (hcmp : PublishedCMPHardness)
    (hp : PlanarSobolev.PublishedNegativePlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hflow : PublishedC4FlowInput) :
    QMAHard unitCoulombCodec.encode unitCoulombPromise := by
  obtain ⟨s,_hs,hsource⟩ := hcmp
  obtain ⟨reduction⟩ := exists_source_unit_reduction_without_hydrogen hflow hp hv
    publishedSobolevSmoothDensity s
  exact hsource.of_reduction reduction

theorem binary_coulomb_qmaHard_of_remaining_inputs
    (hcmp : PublishedCMPHardness)
    (hp : PlanarSobolev.PublishedNegativePlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hflow : PublishedC4FlowInput) :
    QMAHard binaryCoulombCodec.encode binaryCoulombPromise :=
  UnitBinaryProgram.binary_hard_of_unit
    (unit_coulomb_qmaHard_of_remaining_inputs hcmp hp hv hflow)

end ContinuumCoulomb

end

end OAI
