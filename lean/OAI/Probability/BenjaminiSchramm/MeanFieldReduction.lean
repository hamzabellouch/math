import OAI.Probability.BenjaminiSchramm.ProbabilityUpper

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem probabilityLaw_of_critical_volume [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hpc1 : (pc G : ℝ) < 1)
    (hvol : ∀ x, PowerTail (criticalTail G (volumeEvent G) x) (1 / 2)) :
    PercolationProbabilityLaw G := by
  obtain ⟨A,η,hA,hη,hupper⟩ := percolationProbability_upper_of_critical_volume
    G hloc hqt hpc1 hvol
  intro x
  obtain ⟨c,hc,hlower⟩ := percolationProbability_linear_lower G hconn hloc hqt x
  let δ : ℝ := min η ((1-pc G)/2)
  have hδ : 0 < δ := lt_min hη (by positivity)
  refine ⟨c,A,δ,hc,hA,hδ,fun p hp hnear => ?_⟩
  have hnearη : (p : ℝ) - pc G < η := hnear.trans_le (min_le_left _ _)
  have hp1 : p < 1 := by
    have hh := hnear.trans_le (min_le_right η ((1-pc G)/2))
    change (p : ℝ) < 1
    linarith
  exact ⟨hlower p hp hp1,hupper p hp hnearη x⟩

theorem probabilityLaw_of_publishedVolume [Infinite V]
    (G : BondGraph V E) (hgraph : PublishedSimpleGraph G)
    (hvolume : HutchcroftCriticalVolumeInput G) (hgap : pc G < ptwo G) :
    PercolationProbabilityLaw G := by
  let : Countable V := countable_vertices hgraph.locallyFinite hgraph.connected
  let : Countable E := countable_edges hgraph.locallyFinite
  have hp1 : pc G < 1 := hgap.trans_le (ptwo G).2.2
  have hfin := critical_finite_general G hgraph.connected hgraph.locallyFinite
    hgraph.quasiTransitive hp1
  apply probabilityLaw_of_critical_volume G hgraph.connected hgraph.locallyFinite
    hgraph.quasiTransitive hp1
  intro x
  have hh := hvolume hgraph hgap x
  rwa [criticalFiniteTail_eq G (volumeEvent G) x (hfin x)] at hh

theorem full_application_volume_radii [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (hutchcroft2019 :
      ¬ AutUnimodular (subdivision G) (subdivision_injective G)
        (subdivision_connected G hconn) (subdivision_locallyFinite G hloc) →
      pc (subdivision G) < ptwo (subdivision G))
    (hvolume : HutchcroftCriticalVolumeInput (subdivision G))
    (hradii : HutchcroftCriticalRadiiInput (subdivision G)) :
    MainConclusion G ∧ CriticalLawsConclusion G := by
  have hmH := mainConclusion_of_critical_bounded (subdivision G)
    (subdivision_connected G hconn) (subdivision_locallyFinite G hloc)
    (subdivision_quasiTransitive G hloc hqt)
    (critical_subdivision_bounded_conditional G hconn hloc hqt hh hutchcroft2019)
  apply full_application_reduced G hconn hloc hqt hh hutchcroft2019
    (fun hgraph _ => probabilityLaw_of_publishedVolume (subdivision G) hgraph hvolume hmH.2.2.1)
    hvolume hradii

end Percolation.BenjaminiSchramm

end OAI
