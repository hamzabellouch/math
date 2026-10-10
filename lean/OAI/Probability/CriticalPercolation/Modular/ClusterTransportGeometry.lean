import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.Modular.ClusterMassInfinite

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

def small (r : ℕ) (ω : Set E) (v : V) : Prop :=
  ∀ x ∈ G.cluster ω v, ∀ y ∈ G.cluster ω v, y ∈ G.vertexBall x r

lemma small_cluster_subset {r : ℕ} {ω : Set E} {v : V} (h : small G r ω v) :
    G.cluster ω v ⊆ G.vertexBall v r :=
  h v (SimpleGraph.Reachable.refl v)

lemma small_finite (hl : G.LocallyFinite) {r : ℕ} {ω : Set E} {v : V}
    (h : small G r ω v) : (G.cluster ω v).Finite :=
  (G.vertexBall_finite hl v r).subset (small_cluster_subset G h)

lemma small_mono {r R : ℕ} (h : r ≤ R) {ω : Set E} {v : V}
    (hs : small G r ω v) : small G R ω v :=
  fun x hx y hy => G.vertexBall_mono x h (hs x hx y hy)

lemma small_reachable (r : ℕ) {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : small G r ω u ↔ small G r ω v := by
  unfold small
  rw [G.cluster_eq_of_reachable h]

lemma eventually_small (hc : G.fullGraph.Connected) {ω : Set E} {v : V}
    (hC : (G.cluster ω v).Finite) : ∀ᶠ r in atTop, small G r ω v := by
  obtain ⟨n,hn⟩ := G.finite_subset_vertexBall hc v hC
  apply eventually_atTop.mpr
  refine ⟨n+n,fun m hm x hx y hy => ?_⟩
  exact G.vertexBall_mono x hm (G.vertexBall_add ((G.vertexBall_comm).mp (hn hx)) n (hn hy))

lemma small_aut (φ : G.Aut) (r : ℕ) (ω : Set E) (v : V) :
    small G r (φ.edge '' ω) (φ.vertex v) ↔ small G r ω v := by
  unfold small
  rw [← φ.cluster_image]
  constructor
  · intro h x hx y hy
    exact (φ.vertexBall_mem G x y r).mp (h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩)
  · rintro h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact (φ.vertexBall_mem G x y r).mpr (h x hx y hy)

lemma mass_aut (φ : G.Aut) (s : ℕ) (ω : Set E) (v : V) :
    mass G s (φ.edge '' ω) (φ.vertex v) = mass G s ω v := by
  unfold mass size
  rw [← φ.cluster_image,Set.ncard_image_of_injective _ φ.vertex.injective]

lemma coefficient_aut (φ : G.Aut) (p : ℝ) (ω : Set E) (e : E) :
    coefficient p (φ.edge '' ω) (φ.edge e) = coefficient p ω e := by
  simp [coefficient]

lemma incidentCluster_aut (φ : G.Aut) (ω : Set E) (v : V) (e : E) :
    φ.edge e ∈ G.incidentEdges (G.cluster (φ.edge '' ω) (φ.vertex v)) ↔
      e ∈ G.incidentEdges (G.cluster ω v) := by
  rw [← φ.cluster_image]
  simp only [BondGraph.incidentEdges,Set.mem_ofPred_eq,Set.mem_image,φ.preserves,Sym2.mem_map]
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,y,hy,hyx⟩
    exact ⟨x,hx,(φ.vertex.injective hyx) ▸ hy⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨φ.vertex x,⟨x,hx,rfl⟩,x,he,rfl⟩

lemma incidentRoots (ω : Set E) (e : E) :
    {v | e ∈ G.incidentEdges (G.cluster ω v)} =
      G.cluster ω (G.ends e).out.1 ∪ G.cluster ω (G.ends e).out.2 := by
  ext v
  have he : G.ends e = s((G.ends e).out.1,(G.ends e).out.2) := (G.ends e).out_eq.symm
  have hend (x : V) : x ∈ G.ends e ↔ x = (G.ends e).out.1 ∨ x = (G.ends e).out.2 := by
    conv_lhs => rw [he]
    exact Sym2.mem_iff
  simp only [BondGraph.incidentEdges,Set.mem_ofPred_eq,hend,Set.mem_union]
  constructor
  · rintro ⟨x,hx,hx' | hx'⟩
    · subst x; exact Or.inl (SimpleGraph.Reachable.symm hx)
    · subst x; exact Or.inr (SimpleGraph.Reachable.symm hx)
  · rintro (h | h)
    · exact ⟨_,SimpleGraph.Reachable.symm h,Or.inl rfl⟩
    · exact ⟨_,SimpleGraph.Reachable.symm h,Or.inr rfl⟩

variable [Countable V] [Countable E]
lemma measurable_small (r : ℕ) (v : V) : Measurable (fun ω => small G r ω v) := by
  exact Measurable.forall (fun x => (G.measurable_reachable v x).imp
    (Measurable.forall (fun y => (G.measurable_reachable v y).imp measurable_const)))

end CriticalPercolation.FiniteClusters
end
end

end OAI
