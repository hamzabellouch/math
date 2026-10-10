import OAI.Probability.BenjaminiSchramm.OperatorMeanFieldReduction
import OAI.Probability.BenjaminiSchramm.RadiusTransfer

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem full_application_gap [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (hutchcroft2019 :
      ¬ AutUnimodular (subdivision G) (subdivision_injective G)
        (subdivision_connected G hconn) (subdivision_locallyFinite G hloc) →
      pc (subdivision G) < ptwo (subdivision G)) :
    MainConclusion G ∧ CriticalLawsConclusion G := by
  exact full_application_radii G hconn hloc hqt hh hutchcroft2019
    (criticalRadiiInput_of_nonamenable (subdivision G) (subdivision_hV_pos G hloc hqt hh))

end Percolation.BenjaminiSchramm

end OAI
