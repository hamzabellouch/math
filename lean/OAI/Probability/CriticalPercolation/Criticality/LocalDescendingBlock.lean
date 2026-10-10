import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso
import OAI.Probability.CriticalPercolation.ProductMeasure.MeasurableSetRestrict
import OAI.Probability.CriticalPercolation.Gluing.TrialSelection
import OAI.Probability.CriticalPercolation.Criticality.UniformDescendingFan
import OAI.Probability.CriticalPercolation.Exploration.BallIncidence

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def localDescendingFanEvent (v : V) (K ε : ℝ≥0∞) (N R : ℕ) : Set (Set E) :=
  {ω | G.inducedEdges (G.vertexBall v R) ∩ ω ∈ G.descendingFanEvent v K ε N}

lemma localDescendingFanEvent_upper (v : V) (K ε : ℝ≥0∞) (N R : ℕ) :
    IsUpperSet (G.localDescendingFanEvent v K ε N R) := by
  intro ω η h hω
  exact G.descendingFanEvent_upper v K ε N (Set.inter_subset_inter_right _ h) hω

lemma measurableSet_localDescendingFanEvent (hl : G.LocallyFinite)
    (v : V) (K ε : ℝ≥0∞) (N R : ℕ) :
    MeasurableSet (G.localDescendingFanEvent v K ε N R) :=
  BernoulliProduct.measurableSet_restrict _
    (G.finite_inducedEdges hl (G.vertexBall_finite hl v R)) _

lemma tendsto_localDescendingFan (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : unitInterval) (v : V) (K ε : ℝ≥0∞) (N : ℕ) :
    Tendsto (fun R => (G.law p).real (G.localDescendingFanEvent v K ε N R)) atTop
      (𝓝 ((G.law p).real (G.descendingFanEvent v K ε N))) := by
  have h := BernoulliProduct.tendsto_real_finiteWitness p (G.descendingFanEvent v K ε N)
    (G.descendingFanEvent_upper v K ε N) (G.descendingFanEvent_finiteWitness v K ε N)
    (G.inducedBallExhaustion hc hl v)
  have he (n : ℕ) : (G.inducedBallExhaustion hc hl v) n=
      G.inducedEdges (G.vertexBall v n) := rfl
  simpa only [he,BernoulliProduct.law_const,law,localDescendingFanEvent] using h

lemma Aut.localDescendingFanEvent_preimage (φ : G.Aut) (v : V)
    (K ε : ℝ≥0∞) (N R : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.localDescendingFanEvent (φ.vertex v) K ε N R=
      G.localDescendingFanEvent v K ε N R := by
  have he : G.inducedEdges (G.vertexBall (φ.vertex v) R)=
      φ.edge '' G.inducedEdges (G.vertexBall v R) := by
    rw [φ.image_inducedEdges,φ.vertexBall_image]
  ext ω
  change G.inducedEdges (G.vertexBall (φ.vertex v) R)∩(φ.edge '' ω)∈
    G.descendingFanEvent (φ.vertex v) K ε N ↔ _
  rw [he,←Set.image_inter φ.edge.injective]
  exact Set.ext_iff.mp (φ.descendingFanEvent_preimage G v K ε N) _

lemma Aut.localDescendingFanEvent_real [Countable E] (hl : G.LocallyFinite) (φ : G.Aut)
    (p : unitInterval) (v : V) (K ε : ℝ≥0∞) (N R : ℕ) :
    (G.law p).real (G.localDescendingFanEvent (φ.vertex v) K ε N R)=
      (G.law p).real (G.localDescendingFanEvent v K ε N R) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_localDescendingFanEvent hl _ _ _ _ _),φ.localDescendingFanEvent_preimage]

lemma localDescendingFan_uniform_radius [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (K ε : ℝ≥0∞) (N : ℕ) (θ : ℝ)
    (hθ : ∀ v, θ<(G.law p).real (G.descendingFanEvent v K ε N)) :
    ∃ R : ℕ, ∀ v, θ<(G.law p).real (G.localDescendingFanEvent v K ε N R) := by
  have he (v : V) : ∀ᶠ R in atTop, θ<(G.law p).real (G.localDescendingFanEvent v K ε N R) :=
    (G.tendsto_localDescendingFan hc hl p v K ε N).eventually (lt_mem_nhds (hθ v))
  obtain ⟨S,hS,hcover⟩ := hq
  obtain ⟨R,hR⟩ := (hS.toFinset.eventually_all.mpr (fun v _ => he v)).exists
  refine ⟨R,fun v => ?_⟩
  obtain ⟨s,hs,φ,rfl⟩ := hcover v
  rw [φ.localDescendingFanEvent_real G hl]
  exact hR s (hS.mem_toFinset.mpr hs)

def separatedDescendingBlockEvent (v : V) (K ε : ℝ≥0∞) (L N R : ℕ) : Set (Set E) :=
  {ω | ∃ S : Finset V, S.card=N ∧
    (S : Set V).Pairwise (fun x y => y∉G.vertexBall x L) ∧
    ∀ x∈S, x∈G.cluster ((G.inducedEdges (G.vertexBall v R)∩ω)∩
      G.inducedEdges (G.weightCeiling v K)) v ∧ G.stabilizerWeight v x<ε}

lemma separatedDescendingBlockEvent_upper (v : V) (K ε : ℝ≥0∞) (L N R : ℕ) :
    IsUpperSet (G.separatedDescendingBlockEvent v K ε L N R) := by
  rintro ω η h ⟨S,hcard,hsep,hs⟩
  exact ⟨S,hcard,hsep,fun x hx => ⟨G.cluster_mono
    (Set.inter_subset_inter_left _ (Set.inter_subset_inter_right _ h)) v (hs x hx).1,
    (hs x hx).2⟩⟩

lemma separatedDescendingBlockEvent_finiteWitness (v : V) (K ε : ℝ≥0∞) (L N R : ℕ) :
    BernoulliProduct.HasFiniteOpenWitness (G.separatedDescendingBlockEvent v K ε L N R) := by
  rintro ω ⟨S,hcard,hsep,hs⟩
  obtain ⟨J,hJ,hJω,hconn⟩ := G.finite_subset_cluster_finite_witness S.finite_toSet
    (show (S : Set V)⊆G.cluster ((G.inducedEdges (G.vertexBall v R)∩ω)∩
      G.inducedEdges (G.weightCeiling v K)) v from fun x hx => (hs x hx).1)
  refine ⟨J,hJ,(hJω.trans Set.inter_subset_left).trans Set.inter_subset_right,S,hcard,hsep,?_⟩
  have he : (G.inducedEdges (G.vertexBall v R)∩J)∩G.inducedEdges (G.weightCeiling v K)=J := by
    apply Set.Subset.antisymm (Set.inter_subset_left.trans Set.inter_subset_right)
    exact fun e he => ⟨⟨(hJω he).1.1,he⟩,(hJω he).2⟩
  rw [he]
  exact fun x hx => ⟨hconn hx,(hs x hx).2⟩

lemma measurableSet_separatedDescendingBlockEvent [Countable E]
    (v : V) (K ε : ℝ≥0∞) (L N R : ℕ) :
    MeasurableSet (G.separatedDescendingBlockEvent v K ε L N R) :=
  BernoulliProduct.measurableSet_finiteWitness _
    (G.separatedDescendingBlockEvent_upper v K ε L N R)
    (G.separatedDescendingBlockEvent_finiteWitness v K ε L N R)

lemma localDescendingFan_subset_separatedBlock (hl : G.LocallyFinite)
    (L M : ℕ) (hM : 0<M) (hball : ∀ x, (G.vertexBall x L).ncard≤M)
    (v : V) (K ε : ℝ≥0∞) (N R : ℕ) :
    G.localDescendingFanEvent v K ε (M*N) R ⊆
      G.separatedDescendingBlockEvent v K ε L N R := by
  rintro ω ⟨S,hcard,hs⟩
  have hb (x : V) (hx : x∈S) : (S.filter (fun y => y∈G.vertexBall x L)).card≤M := by
    have hh : (↑(S.filter (fun y => y∈G.vertexBall x L)) : Set V) ⊆ G.vertexBall x L :=
      fun y hy => (Finset.mem_filter.mp hy).2
    have hc : (S.filter (fun y => y∈G.vertexBall x L)).card≤(G.vertexBall x L).ncard := by
      simpa only [Set.ncard_coe_finset] using
        Set.ncard_le_ncard hh (G.vertexBall_finite hl x L)
    exact hc.trans (hball x)
  obtain ⟨T,hTS,hTcard,hsep⟩ := CriticalPercolation.separated_subset_of_card
    (fun x y => y∈G.vertexBall x L) (fun x => G.mem_vertexBall_self x L)
    (fun h => G.vertexBall_comm.mp h) M N hM S hb hcard
  exact ⟨T,hTcard,hsep,fun x hx => hs x (hTS hx)⟩

theorem counterexample_separated_downward_blocks
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (hu : ¬G.CombinatoriallyUnimodular)
    (hper : G.law G.criticalProbability G.percolates≠0) :
    ∃ θ : ℝ, 0<θ ∧ ∃ K : ℕ, 1≤K ∧ ∀ ε : ℝ≥0∞, 0<ε → ∀ L N : ℕ,
      ∃ q : unitInterval, (G.criticalProbability : ℝ)/2≤q ∧ q<G.criticalProbability ∧
        ∃ R : ℕ, ∀ v : V,
          θ<(G.law q).real (G.separatedDescendingBlockEvent v K ε L N R) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  obtain ⟨θ,hθ,K,hK,hfan⟩ := G.counterexample_descending_fans_subcritical hc hl hq hpc hu hper
  refine ⟨θ,hθ,K,hK,fun ε hε L N => ?_⟩
  obtain ⟨M,hM⟩ := G.uniform_ball_bound hq L
  obtain ⟨q,hhalf,hqcrit,hqfan⟩ := hfan ε hε ((M+1)*N)
  obtain ⟨R,hR⟩ := G.localDescendingFan_uniform_radius hc hl hq q K ε ((M+1)*N) θ hqfan
  refine ⟨q,hhalf,hqcrit,R,fun v => (hR v).trans_le ?_⟩
  exact measureReal_mono
    (G.localDescendingFan_subset_separatedBlock hl L (M+1) (Nat.succ_pos M)
      (fun v => (hM v).trans (Nat.le_succ M)) v K ε N R) (measure_ne_top _ _)

end CriticalPercolation.BondGraph
end
end

end OAI
