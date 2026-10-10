import OAI.Probability.BenjaminiSchramm.LayerFrontierGeometry
import OAI.Probability.BenjaminiSchramm.SlabFirstVisit
import OAI.Probability.BenjaminiSchramm.HeightOrbitConnection

namespace OAI

noncomputable section
open Set
open scoped Classical

namespace Percolation.BenjaminiSchramm

lemma walk_first_strict_height_peak {V : Type*} {H : SimpleGraph V}
    (f : V → ℝ) {x y : V} (p : H.Walk x y) (t : ℝ)
    (hy : t ≤ f y) :
    ∃ z, t ≤ f z ∧ ∃ q : H.Walk x z, q.length ≤ p.length ∧
      (∀ v ∈ q.support, v ∈ p.support) ∧
      ∀ v ∈ q.support, v ≠ z → f v < f z := by
  let S := p.support.toFinset.filter fun v => t ≤ f v
  have hyS : y ∈ S := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr p.end_mem_support,hy⟩
  obtain ⟨z,hzS,hzp,hfirst⟩ := p.exists_mem_support_forall_mem_support_imp_eq S
    ⟨y,Finset.mem_filter.mpr ⟨hyS,p.end_mem_support⟩⟩
  have hz : t ≤ f z := (Finset.mem_filter.mp hzS).2
  refine ⟨z,hz,p.takeUntil z hzp,p.length_takeUntil_le_length hzp,
    fun v hv => p.support_takeUntil_subset_support hzp hv,?_⟩
  intro v hv hvz
  have hlt : f v < t := by
    by_contra hn
    have hvS : v ∈ S := Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (p.support_takeUntil_subset_support hzp hv),le_of_not_gt hn⟩
    exact hvz (hfirst v hvS hv)
  exact hlt.trans_le hz

variable {V E : Type*} (G : BondGraph V E)

lemma conn_mem_of_open_closed (η : Set E) (U : Set V) (x : V) (hx : x ∈ U)
    (hclosed : ∀ e ∈ η, ∀ v ∈ G e, v ∈ U → ∀ w ∈ G e, w ∈ U) :
    ∀ y, Conn G η x y → y ∈ U := by
  intro y hy
  induction hy with
  | refl => exact hx
  | @tail v w hconn hstep ih =>
    obtain ⟨e,he,heq⟩ := hstep
    exact hclosed e he v (by rw [heq]; simp) ih w (by rw [heq]; simp)

lemma openFrontier_reachable (ω : Set E) (I : Set E) (x : V) {u : V}
    (hu : u ∈ openFrontier G ω (cluster G (ω ∩ I) x)) : Conn G ω x u := by
  obtain ⟨_,v,hv,e,he,heq⟩ := hu
  exact (conn_mono G Set.inter_subset_left hv).tail ⟨e,he,heq⟩

theorem strict_peak_of_lower_frontier_surgery
    (ω η : Set E) (D S F P : Set V) (x u z : V) (f : V → ℝ)
    (hS : cluster G (ω ∩ internalEdges G D) x=S)
    (hF : openFrontier G ω S=F) (hu : u ∈ F)
    (hagree : ∀ e ∈ ballIncidentEdges G S, (e ∈ ω)=(e ∈ η))
    (hpath : Conn G η u z)
    (hclosed : ∀ e ∈ η, ∀ v ∈ G e, v ∈ F ∪ P →
      ∀ w ∈ G e, w ∈ S ∪ F ∪ P)
    (hbelow : ∀ v ∈ S ∪ F, f v < f z)
    (hpeak : ∀ v ∈ P, v ≠ z → f v < f z) :
    Conn G η x z ∧ ∀ y, Conn G η z y → y ≠ z → f y < f z := by
  have hSη : cluster G (η ∩ internalEdges G D) x=S := by
    have hh := restricted_exactCluster_dependsOn G (internalEdges G D) x S hagree
    exact (Iff.of_eq hh).mp hS
  have hFη : openFrontier G η S=F := by
    have hh := openFrontier_dependsOn G S hagree
    exact hh.symm.trans hF
  have huη : u ∈ openFrontier G η (cluster G (η ∩ internalEdges G D) x) := by
    rwa [hSη,hFη]
  have hxz : Conn G η x z := (openFrontier_reachable G η _ x huη).trans hpath
  have hxU : x ∈ S ∪ F ∪ P := Or.inl (Or.inl (hSη ▸ mem_cluster_self G _ x))
  have hclose : ∀ e ∈ η, ∀ v ∈ G e, v ∈ S ∪ F ∪ P →
      ∀ w ∈ G e, w ∈ S ∪ F ∪ P := by
    intro e he v hv hvU w hw
    rcases hvU with (hvS | hvF) | hvP
    · by_cases hwS : w ∈ S
      · exact Or.inl (Or.inl hwS)
      · have hwF : w ∈ F := by
          rw [←hFη]
          have hne : v ≠ w := fun hvw => hwS (hvw ▸ hvS)
          exact ⟨hwS,v,hvS,e,he,(Sym2.mem_and_mem_iff hne).mp ⟨hv,hw⟩⟩
        exact Or.inl (Or.inr hwF)
    · exact hclosed e he v hv (Or.inl hvF) w hw
    · exact hclosed e he v hv (Or.inr hvP) w hw
  refine ⟨hxz,?_⟩
  intro y hzy hyz
  have hyU := conn_mem_of_open_closed G η (S ∪ F ∪ P) x hxU hclose y (hxz.trans hzy)
  rcases hyU with hy | hy
  · exact hbelow y hy
  · exact hpeak y hy hyz

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem stationaryOrbitHeight_peak_extension [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R) :
    ∃ L : ℕ, ∀ x, ∃ z, ∃ w : G.fullGraph.Walk x z,
      w.length ≤ L ∧
      (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v) ∧
      2*R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x z ∧
      ∀ v ∈ w.support, v ≠ z →
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v <
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x z := by
  obtain ⟨A,B,_hA,_hB,hpath⟩ := G.stationaryOrbitHeight_orbit_above hc hl hq μ hμ hstat hu
  obtain ⟨L,hL⟩ := exists_nat_ge (A*(2*R)+B)
  refine ⟨L,fun x => ?_⟩
  obtain ⟨y,p,_horb,hlen,hmin,hy⟩ := hpath (2*R) (by positivity) x (G.vertexOrbit x)
  obtain ⟨z,hz,w,hwlen,hsub,hpeak⟩ := walk_first_strict_height_peak
    (G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x) p (2*R) hy
  refine ⟨z,w,?_,fun v hv => hmin v (hsub v hv),hz,hpeak⟩
  have hpL : p.length ≤ L := by exact_mod_cast hlen.trans hL
  exact hwlen.trans hpL

end CriticalPercolation.BondGraph

end

end OAI
