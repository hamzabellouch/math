import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceConditionalReduction

namespace OAI

/-!
Continuum Coulomb hardness under explicit analytic hypotheses, for the
full spinful weak-H1 infimum and the encoded unit- and binary-charge promises.
-/

noncomputable section
namespace ContinuumCoulomb

theorem conditional_unit_coulomb_qmaHard
    (hcmp : PublishedCMPHardness) (hh : PublishedHydrogenBottom)
    (hp : PlanarSobolev.PublishedNegativePlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    (hflow : PublishedC4FlowInput) : QMAHard unitCoulombCodec.encode unitCoulombPromise := by
  obtain ⟨s,_hs,hsource⟩ := hcmp
  obtain ⟨reduction⟩ := exists_source_unit_reduction hflow hp hv hdensity hh s
  exact hsource.of_reduction reduction

theorem conditional_binary_coulomb_qmaHard
    (hcmp : PublishedCMPHardness) (hh : PublishedHydrogenBottom)
    (hp : PlanarSobolev.PublishedNegativePlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    (hflow : PublishedC4FlowInput) : QMAHard binaryCoulombCodec.encode binaryCoulombPromise :=
  UnitBinaryProgram.binary_hard_of_unit
    (conditional_unit_coulomb_qmaHard hcmp hh hp hv hdensity hflow)

end ContinuumCoulomb

end

end OAI
