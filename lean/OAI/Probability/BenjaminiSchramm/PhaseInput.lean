import OAI.Probability.BenjaminiSchramm.Cayley
import OAI.Probability.CriticalPercolation.Clusters.ClusterNumber

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

def criticalModel (G : BondGraph V E) : CriticalPercolation.BondGraph V E := ⟨G⟩

theorem criticalModel_openGraph (G : BondGraph V E) (ω : Set E) :
    (criticalModel G).openGraph ω = openSimpleGraph G ω := by
  ext x y
  simp only [CriticalPercolation.BondGraph.openGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_image, openSimpleGraph, criticalModel]
  tauto

theorem criticalModel_cluster (G : BondGraph V E) (ω : Set E) (x : V) :
    (criticalModel G).cluster ω x = cluster G ω x := by
  ext y
  simp only [CriticalPercolation.BondGraph.cluster, criticalModel_openGraph,
    Set.mem_ofPred_eq, cluster]
  exact (conn_iff_reachable G ω x y).symm

theorem criticalModel_connected [Nonempty V] (G : BondGraph V E) (hconn : Connected G) :
    (criticalModel G).fullGraph.Connected := by
  rw [CriticalPercolation.BondGraph.fullGraph, criticalModel_openGraph]
  exact ⟨fun x y => (conn_iff_reachable G Set.univ x y).mp (conn_univ_of_connected G hconn x y)⟩

theorem criticalModel_quasiTransitive (G : BondGraph V E) (hqt : QuasiTransitive G) :
    (criticalModel G).QuasiTransitive := by
  obtain ⟨S, hS⟩ := hqt
  refine ⟨S, S.finite_toSet, ?_⟩
  intro x
  obtain ⟨o, ho, a, b, hab, hax⟩ := hS x
  exact ⟨o, ho, ⟨a, b, hab⟩, hax⟩

theorem ae_exists_infinite_cluster_law [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (hp : pc G < p) :
    ∀ᵐ ω ∂law p, ∃ x, (cluster G ω x).Infinite := by
  have h := ae_exists_infinite_cluster_of_pc_lt G p hp
  rw [ae_iff] at h ⊢
  rw [← map_openEdges p, Measure.map_apply (measurable_openEdges p)
    (show MeasurableSet {ω : Set E | ¬ ∃ x, (cluster G ω x).Infinite} from
      (measurableSet_exists_infinite_cluster G).compl)]
  exact h

theorem infiniteClusters_infinite_of_criticalModel (G : BondGraph V E) (ω : Set E)
    (h : (criticalModel G).infinitelyManyInfiniteClusters ω) :
    (infiniteClusters G ω).Infinite := by
  classical
  intro hf
  let C := infiniteClusters G ω
  let : Fintype C := hf.fintype
  let root : C → V := fun c => Classical.choose c.property.2
  let S : Finset V := Finset.univ.image root
  obtain ⟨v, hv, havoid⟩ := h S
  rw [criticalModel_cluster] at hv
  let c : C := ⟨cluster G ω v, hv, v, rfl⟩
  have hc : cluster G ω v = cluster G ω (root c) := Classical.choose_spec c.property.2
  have hr : root c ∈ S := Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
  apply havoid (root c) hr
  rw [criticalModel_openGraph]
  apply (conn_iff_reachable G ω v (root c)).mp
  change root c ∈ cluster G ω v
  rw [hc]
  exact mem_cluster_self G ω (root c)

theorem publishedPhaseInput_proved [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) : PublishedPhaseInput G := by
  classical
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  intro p hp hpu
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (pc G).2.1 hp
  have hc := criticalModel_connected G hconn
  have hq := criticalModel_quasiTransitive G hqt
  rcases (criticalModel G).unique_or_infinitely_many_ae hc hloc hq p hp0 with hu | hi
  · have hex := ae_exists_infinite_cluster_law G p hp
    have hunique : ∀ᵐ ω ∂law p, ∃! C, C ∈ infiniteClusters G ω := by
      filter_upwards [hu, hex] with ω hω hωinf
      obtain ⟨x, hx⟩ := hωinf
      refine ⟨cluster G ω x, ⟨hx, x, rfl⟩, ?_⟩
      rintro C ⟨hC, y, rfl⟩
      apply cluster_eq_of_conn G ω
      apply (conn_iff_reachable G ω y x).mpr
      rw [← criticalModel_openGraph]
      apply hω y x
      · rwa [criticalModel_cluster]
      · rwa [criticalModel_cluster]
    have hprob : law p {ω | ∃! C, C ∈ infiniteClusters G ω} = 1 := by
      calc
        _ = (law p : Measure (Set E)) Set.univ := by
          apply measure_congr
          filter_upwards [hunique] with ω hω
          exact propext (iff_true_intro hω)
        _ = 1 := measure_univ
    exact False.elim (not_le_of_gt hpu (sInf_le hprob))
  · exact hi.mono (fun ω hω => infiniteClusters_infinite_of_criticalModel G ω hω)

end Percolation.BenjaminiSchramm

end OAI
