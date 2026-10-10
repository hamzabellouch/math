import OAI.Analysis.CoulombTransport.ActualGeometryConclusion

namespace OAI

namespace Problem356

theorem coulomb_counterexample_and_equal_infima :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by
  exact FiveComponentGeometry.exists_full_coulomb_conclusion

end Problem356

end OAI
