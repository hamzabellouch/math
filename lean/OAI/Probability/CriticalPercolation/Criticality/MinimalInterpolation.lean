import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.InterpolationUniform
import OAI.Probability.CriticalPercolation.Criticality.MinimalPair
import OAI.Probability.CriticalPercolation.Criticality.InfiniteInterpolation
import OAI.Probability.CriticalPercolation.Clusters.ClusterTail
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable E] (G : BondGraph V E)

lemma maximal_interpolation_pair (p : unitInterval) (hp : (p:ℝ)∈Set.Ioo 0 1)
    (s r : ℕ) {a c t ε : ℝ} (ha : 0<a) (hc : 0<c) (ht : 0≤t)
    (hε : 0<ε) (hεp : ε≤p) (hεq : ε≤1-(p:ℝ)) (hac : a≤c) (hct : 2*c≤t^2)
    (htail : ∀ v, t≤(G.law p).real (G.clusterTail v s))
    (hex : ∃ u v, v∈G.vertexBall u r ∧ a≤(G.law p).real (G.twoClusterEvent u v s)) :
    ∃ u v, G.fullGraph.Adj u v ∧ 0<(G.law p).real (G.twoClusterEvent u v s) ∧
      -Real.log ((G.law p).real (G.twoClusterEvent u v s)) ≤
        max 1 (interpolationConstant (c/2) ε) * (Real.log (1/a)+Nat.clog 2 r+1) := by
  obtain ⟨u,v,w,hwpos,hwr,hδ,hmin⟩ := G.exists_minimal_pair p s r a ha hex
  have hδpos : 0<(G.law p).real (G.twoClusterEvent u v s) := ha.trans_le hδ
  have ha1 : a≤1 := hδ.trans measureReal_le_one
  have halog : 0≤Real.log (1/a) := Real.log_nonneg ((le_div_iff₀ ha).mpr (by linarith))
  have hbnon : 0≤Real.log (1/a)+(Nat.clog 2 r:ℝ)+1 := by positivity
  have hlog : -Real.log ((G.law p).real (G.twoClusterEvent u v s))≤Real.log (1/a) := by
    rw [one_div,Real.log_inv]
    exact neg_le_neg (Real.log_le_log ha hδ)
  by_cases hd : w.length=1
  · refine ⟨u,v,?_,hδpos,?_⟩
    · have hh := w.adj_getVert_succ (by omega : 0<w.length)
      simpa only [SimpleGraph.Walk.getVert_zero,← hd,Nat.zero_add,SimpleGraph.Walk.getVert_length] using hh
    · calc
        _ ≤ Real.log (1/a) := hlog
        _ ≤ Real.log (1/a)+(Nat.clog 2 r:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) (Nat.clog 2 r); linarith
        _ ≤ _ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (le_max_left 1 (interpolationConstant (c/2) ε)) hbnon
  · have hconn : ∀ j k, j<k → k≤w.length → k-j<w.length →
        c≤(G.law p).real {ω | (G.openGraph ω).Reachable (w.getVert j) (w.getVert k)} := by
      intro j k hjk hk hdiff
      have hm := hmin (w.getVert j) (w.getVert k) (k-j) hdiff
        (G.walk_getVert_mem_vertexBall w j k hjk.le hk)
      have hh := G.connection_lower_of_twoCluster p (w.getVert j) (w.getVert k) s t a ht
        (htail _) (htail _) hm.le
      linarith
    have hδ' : 0<(G.law p).real (G.twoClusterEvent (w.getVert 0) (w.getVert w.length) s) := by
      simpa only [SimpleGraph.Walk.getVert_zero,SimpleGraph.Walk.getVert_length] using hδpos
    obtain ⟨j,hj,hjp,hjl⟩ := G.infinite_interpolation_measure w.length w.getVert (by omega) p hp
      hc hε hεp hεq hconn s hδ'
    refine ⟨w.getVert j,w.getVert (j+1),w.adj_getVert_succ hj,hjp,?_⟩
    simp only [SimpleGraph.Walk.getVert_zero,SimpleGraph.Walk.getVert_length,one_div,Real.log_inv] at hjl
    have hclog : (Nat.clog 2 w.length:ℝ)≤Nat.clog 2 r := Nat.cast_le.mpr (Nat.clog_mono_right 2 hwr)
    calc
      _ ≤ interpolationConstant (c/2) ε *
        (-Real.log ((G.law p).real (G.twoClusterEvent u v s))+(Nat.clog 2 w.length:ℝ)+1) := hjl
      _ ≤ interpolationConstant (c/2) ε * (Real.log (1/a)+(Nat.clog 2 r:ℝ)+1) :=
        mul_le_mul_of_nonneg_left (by linarith) (interpolationConstant_pos _ hε).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hbnon

end CriticalPercolation.BondGraph
end
end
end

end OAI
