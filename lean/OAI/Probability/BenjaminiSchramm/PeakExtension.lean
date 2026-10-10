import OAI.Probability.BenjaminiSchramm.PeakSurgeryGeometry

namespace OAI

noncomputable section
open Set
open scoped Classical

namespace Percolation.BenjaminiSchramm

lemma walk_first_height_prefix {V : Type*} {H : SimpleGraph V}
    (f : V → ℝ) {x y : V} (p : H.Walk x y) (t : ℝ) (hy : t ≤ f y) :
    ∃ z, t ≤ f z ∧ ∃ q : H.Walk x z, q.length ≤ p.length ∧
      (∀ v ∈ q.support, v ∈ p.support) ∧
      ∀ v ∈ q.support, v ≠ z → f v < t := by
  let S := p.support.toFinset.filter fun v => t ≤ f v
  have hyS : y ∈ S := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr p.end_mem_support,hy⟩
  obtain ⟨z,hzS,hzp,hfirst⟩ := p.exists_mem_support_forall_mem_support_imp_eq S
    ⟨y,Finset.mem_filter.mpr ⟨hyS,p.end_mem_support⟩⟩
  have hz : t ≤ f z := (Finset.mem_filter.mp hzS).2
  refine ⟨z,hz,p.takeUntil z hzp,p.length_takeUntil_le_length hzp,
    fun v hv => p.support_takeUntil_subset_support hzp hv,?_⟩
  intro v hv hvz
  by_contra hn
  have hvS : v ∈ S := Finset.mem_filter.mpr
    ⟨List.mem_toFinset.mpr (p.support_takeUntil_subset_support hzp hv),le_of_not_gt hn⟩
  exact hvz (hfirst v hvS hv)

variable {V E : Type*} (G : BondGraph V E)

lemma lowerFrontierCell_height_bounds (f : V → ℝ) (R b : ℝ)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e → |f w-f v| ≤ R)
    (x : V) (hx : f x ≤ b) (S F : Set V) {ω : Set E}
    (hcell : ω ∈ lowerFrontierCell G (internalEdges G {v | f v ≤ b}) Set.univ x S F)
    (u : V) (hu : u ∈ F) : b < f u ∧ f u ≤ b+R := by
  have hF : openFrontier G ω S=F := by simpa only [Set.inter_univ] using hcell.2
  have huF : u ∈ openFrontier G ω (cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x) := by
    rwa [hcell.1,hF]
  have huout := openFrontier_lowerCluster_outside G ω {v | f v ≤ b} x hx huF
  obtain ⟨_,v,hv,e,he,heq⟩ := huF
  have hvb := conn_internalEdges_end_mem G ω {v | f v ≤ b} hx hv
  have hj := (abs_le.mp (hjump e v u (by rw [heq]; simp) (by rw [heq]; simp))).2
  change ¬f u ≤ b at huout
  change f v ≤ b at hvb
  exact ⟨lt_of_not_ge huout,by linarith⟩

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem stationaryOrbitHeight_bounded_peak_extension [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ L : ℕ, ∀ x, ∃ z, ∃ w : G.fullGraph.Walk x z,
      w.length ≤ L ∧
      (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v) ∧
      (2*R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x z ∧
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x z ≤ 3*R) ∧
      ∀ v ∈ w.support, v ≠ z →
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v <
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x z := by
  obtain ⟨L,hpath⟩ := G.stationaryOrbitHeight_peak_extension hc hl hq μ hμ hstat hu R hR
  refine ⟨L,fun x => ?_⟩
  obtain ⟨y,p,hlen,hmin,hy,_hpeak⟩ := hpath x
  let f := G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x
  obtain ⟨z,hz,w,hwlen,hsub,hbelow⟩ := walk_first_height_prefix f p (2*R) hy
  have hj {v v' : V} (hv : G.fullGraph.Adj v v') : |f v'-f v| ≤ R := by
    obtain ⟨⟨e,_he,heq⟩,_hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hv
    have hh := hjump e v v' (by rw [heq]; simp) (by rw [heq]; simp)
    have he : f v'-f v=G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v v' := by
      dsimp [f]
      rw [G.orbitAdjustedHeight_change_base hc hl _ x v v',add_sub_cancel_left]
    rwa [he]
  have hzupper : f z ≤ 2*R+R := walk_endpoint_height_bound f R (2*R) hR.le hj w
    (by simp only [f,G.orbitAdjustedHeight_self]; positivity) hbelow
  refine ⟨z,w,hwlen.trans hlen,fun v hv => hmin v (hsub v hv),⟨hz,by linarith⟩,?_⟩
  intro v hv hvz
  exact (hbelow v hv hvz).trans_le hz

end CriticalPercolation.BondGraph

end

end OAI
