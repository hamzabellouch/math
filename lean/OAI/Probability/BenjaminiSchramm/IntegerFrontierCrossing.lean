import OAI.Probability.BenjaminiSchramm.PeakExtension
import OAI.Probability.BenjaminiSchramm.LayerFrontierExpectation
import OAI.Probability.BenjaminiSchramm.LayerMomentCauchy

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma integer_lower_frontier_level (f : V → ℤ) (n : ℤ)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e → f w ≤ f v+1)
    (ω : Set E) (x : V) (hx : f x < n) {u : V}
    (hu : u ∈ openFrontier G ω (cluster G (ω ∩ internalEdges G {v | f v < n}) x)) : f u=n := by
  have hout := openFrontier_lowerCluster_outside G ω {v | f v < n} x hx hu
  obtain ⟨_,v,hv,e,_he,heq⟩ := hu
  have hvn := conn_internalEdges_end_mem G ω {v | f v < n} hx hv
  have hj := hjump e v u (by rw [heq]; simp) (by rw [heq]; simp)
  change ¬f u < n at hout
  change f v < n at hvn
  omega

lemma integer_frontierCount_le_fullLayerCount [Countable V] [Countable E]
    (f : V → ℤ) (n : ℤ)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e → f w ≤ f v+1)
    (ω : Set E) (x : V) (hx : f x < n) :
    frontierCount G (internalEdges G {v | f v < n}) Set.univ ω x ≤
      restrictedLayerCount G Set.univ {v | f v=n} ω x := by
  apply ENNReal.tsum_le_tsum
  intro u
  by_cases hu : u ∈ openFrontier G (ω ∩ Set.univ)
      (cluster G (ω ∩ internalEdges G {v | f v < n}) x)
  · have hu' : u ∈ openFrontier G ω (cluster G (ω ∩ internalEdges G {v | f v < n}) x) := by
      simpa only [Set.inter_univ] using hu
    have hn := integer_lower_frontier_level G f n hjump ω x hx hu'
    have hc := openFrontier_reachable G ω (internalEdges G {v | f v < n}) x hu'
    simp only [Set.mem_ofPred_eq,Set.inter_univ,ite_eq_left hu',ite_eq_left (show f u=n ∧ Conn G ω x u from ⟨hn,hc⟩),le_refl]
  · rw [ite_eq_right hu]
    exact bot_le

lemma integer_upper_layer_hit_frontier_probability [Countable V] [Countable E]
    (f : V → ℤ) (n : ℤ) (x : V) (hx : f x < n) (p : unitInterval) :
    law p (restrictedHit G (internalEdges G {v | f v ≤ n}) x {v | f v=n}) ≤
      law p {ω | 0 < frontierCount G (internalEdges G {v | f v < n}) Set.univ ω x} := by
  apply measure_mono
  rintro ω ⟨y,hy,hxy⟩
  let S := cluster G (ω ∩ internalEdges G {v | f v < n}) x
  have hyS : y ∉ S := by
    intro h
    have hh := conn_internalEdges_end_mem G ω {v | f v < n} hx h
    change f y < n at hh
    change f y=n at hy
    omega
  obtain ⟨u,hu,_huy⟩ := conn_last_exit_frontier G ω S (mem_cluster_self G _ x) hyS
    (conn_mono G Set.inter_subset_left hxy)
  have hone : (1 : ℝ≥0∞) ≤ frontierCount G (internalEdges G {v | f v < n}) Set.univ ω x := by
    apply le_trans _ (ENNReal.le_tsum u)
    have hu' : u ∈ openFrontier G (ω ∩ Set.univ) S := by simpa only [Set.inter_univ] using hu
    exact (ite_eq_left hu').symm.le
  exact zero_lt_one.trans_le hone

end Percolation.BenjaminiSchramm

end

end OAI
