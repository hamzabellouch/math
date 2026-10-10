import OAI.Probability.BenjaminiSchramm.Application
import OAI.Probability.BenjaminiSchramm.GeneralCriticalFiniteness
import OAI.Probability.BenjaminiSchramm.SusceptibilityLaw

namespace OAI

namespace Percolation.BenjaminiSchramm

open MeasureTheory

universe u v
variable {V : Type u} {E : Type v}

theorem susceptibilityLaw_of_publishedVolume [Infinite V]
    (G : BondGraph V E) (hgraph : PublishedSimpleGraph G)
    (hvolume : HutchcroftCriticalVolumeInput G) (hgap : pc G < ptwo G) :
    SusceptibilityLaw G := by
  let : Countable V := countable_vertices hgraph.locallyFinite hgraph.connected
  let : Countable E := countable_edges hgraph.locallyFinite
  have hp1 : pc G < 1 := hgap.trans_le (ptwo G).2.2
  have hfin := critical_finite_general G hgraph.connected hgraph.locallyFinite
    hgraph.quasiTransitive hp1
  apply susceptibilityLaw_of_critical_volume G hgraph.connected hgraph.locallyFinite
    hgraph.quasiTransitive hp1
  intro x
  have hh := hvolume hgraph hgap x
  rwa [criticalFiniteTail_eq G (volumeEvent G) x (hfin x)] at hh

theorem firstMomentInput_of_volume [Infinite V]
    (G : BondGraph V E) (hvolume : HutchcroftCriticalVolumeInput G) :
    HutchcroftFirstMomentInput G := by
  intro hgraph hgap x
  let : Countable V := countable_vertices hgraph.locallyFinite hgraph.connected
  let : Countable E := countable_edges hgraph.locallyFinite
  obtain ⟨c,C,δ,hc,hC,hδ,hb⟩ := susceptibilityLaw_of_publishedVolume G hgraph hvolume hgap x
  refine ⟨c,C,δ,hc,hC,hδ,fun p hp hnear => ?_⟩
  rw [←(susceptibility_eq_integral G hgraph.locallyFinite hgraph.quasiTransitive p hp x).2]
  exact hb p hp hnear

theorem full_application_reduced [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (hutchcroft2019 :
      ¬ AutUnimodular (subdivision G) (subdivision_injective G)
        (subdivision_connected G hconn) (subdivision_locallyFinite G hloc) →
      pc (subdivision G) < ptwo (subdivision G))
    (htheta : TrianglePercolationProbabilityInput (subdivision G))
    (hvolume : HutchcroftCriticalVolumeInput (subdivision G))
    (hradii : HutchcroftCriticalRadiiInput (subdivision G)) :
    MainConclusion G ∧ CriticalLawsConclusion G :=
  full_application_conditional G hconn hloc hqt hh hutchcroft2019
    (firstMomentInput_of_volume (subdivision G) hvolume) htheta hvolume hradii

end Percolation.BenjaminiSchramm

end OAI
