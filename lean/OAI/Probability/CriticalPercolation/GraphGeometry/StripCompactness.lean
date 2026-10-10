import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterTail
import OAI.Probability.CriticalPercolation.ProductMeasure.LevelContactMeasurability
import OAI.Probability.CriticalPercolation.Criticality.OpenRay
import OAI.Probability.CriticalPercolation.Criticality.RestrictedSeed
import OAI.Probability.CriticalPercolation.Gluing.MoveWitness

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def seedDomainTail (A S : Set V) (n : ℕ) : Set (Set E) :=
  ⋃ a∈A, (fun ω : Set E => ω∩G.inducedEdges S) ⁻¹' G.clusterTail a n

def seedDomainInfinite (A S : Set V) : Set (Set E) :=
  {ω | ∃ a∈A, (G.cluster (ω∩G.inducedEdges S) a).Infinite}

lemma seedDomainTail_measurable [Countable V] [Countable E] (A S : Set V) (n : ℕ) :
    MeasurableSet (G.seedDomainTail A S n) := by
  have hm : Measurable (fun ω : Set E => ω∩G.inducedEdges S) :=
    (BernoulliProduct.measurable_inter_block _).mono (BernoulliProduct.blockSigma_le _) le_rfl
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ =>
    (G.measurableSet_clusterTail a n).preimage hm

lemma seedDomainTail_antitone (A S : Set V) : Antitone (G.seedDomainTail A S) := by
  intro n m hnm ω hω
  obtain ⟨a,ha,ht⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨a,ha,G.clusterTail_antitone a hnm ht⟩

lemma seedDomainInfinite_eq_iInter (A S : Set V) (hA : A.Finite) :
    G.seedDomainInfinite A S=⋂ n, G.seedDomainTail A S n := by
  ext ω
  constructor
  · rintro ⟨a,ha,hi⟩
    exact Set.mem_iInter.mpr fun n => Set.mem_iUnion₂.mpr
      ⟨a,ha,G.infiniteEvent_subset_clusterTail a n hi⟩
  · intro hω
    by_contra hn
    have hf : ∀ a∈A, (G.cluster (ω∩G.inducedEdges S) a).Finite := by
      intro a ha
      by_contra hi
      exact hn ⟨a,ha,hi⟩
    let K := ⋃ a∈A, G.cluster (ω∩G.inducedEdges S) a
    have hK : K.Finite := hA.biUnion hf
    obtain ⟨a,ha,L,hL,hLa,hLn⟩ := Set.mem_iUnion₂.mp
      (Set.mem_iInter.mp hω (K.ncard+1))
    have hs : L⊆K := fun x hx => Set.mem_iUnion₂.mpr ⟨a,ha,hLa hx⟩
    have hc := Set.ncard_le_ncard hs hK
    omega

lemma seedDomainInfinite_probability [Countable V] [Countable E]
    (μ : Measure (Set E)) [IsFiniteMeasure μ] (A S : Set V) (hA : A.Finite)
    (r : ℝ) (h : ∀ n, r≤μ.real (G.seedDomainTail A S n)) :
    r≤μ.real (G.seedDomainInfinite A S) := by
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (G.seedDomainTail_measurable A S n).nullMeasurableSet)
    (G.seedDomainTail_antitone A S) ⟨0,measure_ne_top _ _⟩
  rw [←G.seedDomainInfinite_eq_iInter A S hA] at ht
  exact ge_of_tendsto ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht)
    (Filter.Eventually.of_forall h)

lemma RayPrefix.reachable {ω : Set E} {a : V} {n : ℕ} (p : G.RayPrefix ω a n)
    (i : Fin (n+1)) : (G.openGraph ω).Reachable a (p.vertex i) := by
  suffices hh : ∀ k, ∀ hk : k<n+1, (G.openGraph ω).Reachable a (p.vertex ⟨k,hk⟩) from
    hh i.val i.isLt
  intro k
  induction k with
  | zero =>
    intro hk
    have he : (⟨0,hk⟩ : Fin (n+1))=0 := by ext; simp
    rw [he,p.start]
  | succ k ih =>
    intro hk
    exact (ih (by omega)).trans (p.adjacent ⟨k,by omega⟩).reachable

lemma RayPrefix.clusterTail {ω : Set E} {a : V} {n : ℕ} (p : G.RayPrefix ω a n) :
    ω∈G.clusterTail a (n+1) := by
  refine ⟨Set.range p.vertex,Set.finite_range _,?_,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact p.reachable G i
  · rw [Set.ncard_range_of_injective p.injective,Nat.card_fin]

lemma exit_gives_prefix (A S K : Set V) (n : ℕ)
    (hK : ∀ a∈A, G.vertexBall a n⊆K) {ω : Set E}
    (hω : ω∈G.restrictedSeed A (S\K) (G.inducedEdges S)) :
    ∃ a∈A, ∃ p : G.RayPrefix ω a n, ∀ i, p.vertex i∈S∩K := by
  obtain ⟨a,ha,b,⟨w⟩,hb⟩ := Set.mem_iUnion₂.mp hω
  let p := w.toPath
  let q := p.val.mapLe (G.openGraph_mono Set.inter_subset_left)
  have hlen : n<q.length := by
    by_contra hn
    have h := G.openWalk_getVert_ball q q.length le_rfl
    rw [SimpleGraph.Walk.getVert_length] at h
    exact hb.2 (hK a ha (G.vertexBall_mono a (by omega) h))
  let r : G.RayPrefix ω a n := {
    vertex := fun i => q.getVert i.val
    start := q.getVert_zero
    adjacent := fun i => q.adj_getVert_succ (by omega)
    injective := by
      intro i j hij
      apply Fin.ext
      have hpath : q.IsPath := p.property.mapLe _
      exact hpath.getVert_injOn (by change i.val≤q.length; omega)
        (by change j.val≤q.length; omega) hij
    ball := fun i => G.openWalk_getVert_ball q i.val (by omega) }
  refine ⟨a,ha,r,?_⟩
  intro i
  refine ⟨?_,hK a ha (G.vertexBall_mono a (by omega) (r.ball i))⟩
  have hs := G.walk_induced_support p.val hb.1 (p.val.getVert i.val)
    (p.val.getVert_mem_support i.val)
  simpa only [r,q,SimpleGraph.Walk.mapLe,SimpleGraph.Walk.getVert_map,SimpleGraph.Hom.ofLE_apply] using hs

def prefix_inside_domain {ω : Set E} {a : V} {n : ℕ} (p : G.RayPrefix ω a n)
    (S : Set V) (hS : ∀ i, p.vertex i∈S) :
    G.RayPrefix (ω∩G.inducedEdges S) a n := {
  vertex := p.vertex, start := p.start, injective := p.injective, ball := p.ball
  adjacent := fun i => (G.open_induced_adj S ω _ _).mpr
    ⟨p.adjacent i,hS i.castSucc,hS i.succ⟩ }

theorem local_domain_exit_compactness [Countable V] [Countable E]
    (hl : G.LocallyFinite) (μ : Measure (Set E)) [IsFiniteMeasure μ]
    (A S : Set V) (hA : A.Finite) (Sj Tj : ℕ → Set V) (r : ℝ)
    (hlocal : ∀ K : Set V, K.Finite → ∀ᶠ j in atTop, Sj j∩K⊆S)
    (hescape : ∀ K : Set V, K.Finite → ∀ᶠ j in atTop, Disjoint (Tj j) K)
    (hprob : ∀ j, r≤μ.real (G.restrictedSeed A (Sj j∩Tj j) (G.inducedEdges (Sj j)))) :
    r≤μ.real (G.seedDomainInfinite A S) := by
  apply G.seedDomainInfinite_probability μ A S hA r
  intro n
  let K := ⋃ a∈A, G.vertexBall a n
  have hK : K.Finite := hA.biUnion (fun a _ => G.vertexBall_finite hl a n)
  obtain ⟨j,hj,hj'⟩ := ((hlocal K hK).and (hescape K hK)).exists
  apply (hprob j).trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  have hout : ω∈G.restrictedSeed A (Sj j\K) (G.inducedEdges (Sj j)) := by
    obtain ⟨a,ha,b,hr,hb⟩ := Set.mem_iUnion₂.mp hω
    exact Set.mem_iUnion₂.mpr ⟨a,ha,b,hr,hb.1,fun hk => Set.disjoint_left.mp hj' hb.2 hk⟩
  obtain ⟨a,ha,p,hp⟩ := G.exit_gives_prefix A (Sj j) K n
    (fun a ha x hx => Set.mem_iUnion₂.mpr ⟨a,ha,hx⟩) hout
  have ht := (G.prefix_inside_domain p S (fun i => hj (hp i))).clusterTail G
  exact Set.mem_iUnion₂.mpr ⟨a,ha,G.clusterTail_antitone a (Nat.le_succ n) ht⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
