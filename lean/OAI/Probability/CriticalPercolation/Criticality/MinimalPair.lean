import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterTail
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneIndicatorUpper

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma walk_mem_vertexBall {u v : V} (w : G.fullGraph.Walk u v) :
    v∈G.vertexBall u w.length := by
  induction w with
  | nil => exact G.mem_vertexBall_self _ 0
  | @cons u v z h w ih =>
    have hv := G.vertexBall_step (G.mem_vertexBall_self u 0) h
    simpa only [SimpleGraph.Walk.length_cons,Nat.add_comm] using G.vertexBall_add hv w.length ih

lemma mem_vertexBall_iff_walk {u v : V} {n : ℕ} :
    v∈G.vertexBall u n ↔ ∃ w : G.fullGraph.Walk u v, w.length≤n := by
  constructor
  · intro hv
    induction n generalizing v with
    | zero =>
      have he : v=u := hv
      subst v
      exact ⟨.nil,le_rfl⟩
    | succ n ih =>
      rcases hv with hv|hv
      · obtain ⟨w,hw⟩ := ih hv
        exact ⟨w,hw.trans (Nat.le_succ _)⟩
      · obtain ⟨z,hz,hzv⟩ := Set.mem_iUnion₂.mp hv
        obtain ⟨w,hw⟩ := ih hz
        have hzv' : G.fullGraph.Adj z v := hzv
        exact ⟨SimpleGraph.Walk.concat w hzv', by
          rw [SimpleGraph.Walk.length_concat]
          exact Nat.add_le_add_right hw 1⟩
  · rintro ⟨w,hw⟩
    exact G.vertexBall_mono u hw (G.walk_mem_vertexBall w)

lemma walk_getVert_mem_vertexBall {u v : V} (w : G.fullGraph.Walk u v)
    (j k : ℕ) (hjk : j≤k) (hk : k≤w.length) :
    w.getVert k∈G.vertexBall (w.getVert j) (k-j) := by
  have hh : ∀ n, j+n≤w.length →
      w.getVert (j+n)∈G.vertexBall (w.getVert j) n := by
    intro n
    induction n with
    | zero => intro _; simpa only [Nat.add_zero] using G.mem_vertexBall_self (w.getVert j) 0
    | succ n ih =>
      intro hn
      have hs := G.vertexBall_step (ih (by omega)) (w.adj_getVert_succ (by omega : j+n<w.length))
      simpa only [Nat.add_assoc,Nat.succ_eq_add_one] using hs
  simpa only [Nat.add_sub_of_le hjk] using hh (k-j) (by omega)

lemma twoClusterEvent_self (u : V) (s : ℕ) : G.twoClusterEvent u u s=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω hω
  exact hω.1.1 (SimpleGraph.Reachable.refl _)

lemma twoClusterEvent_antitone (u v : V) : Antitone (G.twoClusterEvent u v) := by
  intro s t hst ω hω
  exact ⟨⟨hω.1.1,G.clusterTail_antitone u hst hω.1.2⟩,G.clusterTail_antitone v hst hω.2⟩

lemma exists_minimal_pair (p : unitInterval) (s r : ℕ) (a : ℝ) (ha : 0<a)
    (hex : ∃ u v, v∈G.vertexBall u r ∧ a≤(G.law p).real (G.twoClusterEvent u v s)) :
    ∃ (u v : V) (w : G.fullGraph.Walk u v), 1≤w.length ∧ w.length≤r ∧
      a≤(G.law p).real (G.twoClusterEvent u v s) ∧
      ∀ x y k, k<w.length → y∈G.vertexBall x k →
        (G.law p).real (G.twoClusterEvent x y s)<a := by
  let P (n : ℕ) := ∃ u v, v∈G.vertexBall u n ∧ a≤(G.law p).real (G.twoClusterEvent u v s)
  have hP : ∃ n, P n := ⟨r,hex⟩
  let d := Nat.find hP
  obtain ⟨u,v,hv,ha'⟩ := Nat.find_spec hP
  obtain ⟨w,hw⟩ := G.mem_vertexBall_iff_walk.mp hv
  have hwd : w.length=d := le_antisymm hw (Nat.find_min' hP ⟨u,v,G.walk_mem_vertexBall w,ha'⟩)
  have hpos : 0<d := by
    by_contra! hd
    have hd0 : d=0 := Nat.eq_zero_of_le_zero hd
    have huv : v=u := by
      change v∈G.vertexBall u d at hv
      simpa only [hd0,vertexBall,Set.mem_singleton_iff] using hv
    subst v
    rw [G.twoClusterEvent_self,measureReal_empty] at ha'
    linarith
  refine ⟨u,v,w,by omega,hwd.le.trans (Nat.find_min' hP hex),ha',?_⟩
  intro x y k hk hxy
  apply lt_of_not_ge
  intro hh
  exact Nat.find_min hP (by omega) ⟨x,y,hxy,hh⟩

lemma connection_lower_of_twoCluster [Countable E] (p : unitInterval)
    (u v : V) (s : ℕ) (t a : ℝ) (ht : 0≤t)
    (hu : t≤(G.law p).real (G.clusterTail u s))
    (hv : t≤(G.law p).real (G.clusterTail v s))
    (hsep : (G.law p).real (G.twoClusterEvent u v s)≤a) :
    t^2-a≤(G.law p).real {ω | (G.openGraph ω).Reachable u v} := by
  have hh := BernoulliProduct.harris_finiteWitness (fun _ : E => p)
    (G.clusterTail u s) (G.clusterTail v s) (G.clusterTail_isUpperSet u s)
    (G.clusterTail_isUpperSet v s) (G.clusterTail_hasFiniteOpenWitness u s)
    (G.clusterTail_hasFiniteOpenWitness v s)
  rw [BernoulliProduct.law_const] at hh
  have hm : G.clusterTail u s∩G.clusterTail v s ⊆
      {ω | (G.openGraph ω).Reachable u v}∪G.twoClusterEvent u v s := by
    intro ω hω
    by_cases hc : (G.openGraph ω).Reachable u v
    · exact Or.inl hc
    · exact Or.inr ⟨⟨hc,hω.1⟩,hω.2⟩
  have hbound := (measureReal_mono hm (μ := G.law p)).trans
    (measureReal_union_le _ _)
  change (G.law p).real (G.clusterTail u s)*(G.law p).real (G.clusterTail v s) ≤
    (G.law p).real (G.clusterTail u s∩G.clusterTail v s) at hh
  have hprod : t^2≤(G.law p).real (G.clusterTail u s)*(G.law p).real (G.clusterTail v s) := by
    simpa only [pow_two] using mul_le_mul hu hv ht (ht.trans hu)
  linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
