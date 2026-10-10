import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.PercolationTail
import OAI.Probability.CriticalPercolation.Gluing.MoveExit
import OAI.Probability.CriticalPercolation.Gluing.MoveWitness
import OAI.Probability.CriticalPercolation.Gluing.RelayMoves
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso
import OAI.Probability.CriticalPercolation.ProductMeasure.LevelContactMeasurability

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_induced_subset (ω : Set E) (S : Set V) {a : V} (ha : a∈S) :
    G.cluster (ω∩G.inducedEdges S) a⊆S := by
  rintro b ⟨w⟩
  exact G.walk_induced_support w.reverse ha b w.reverse.start_mem_support

lemma infinite_strip_unbounded (u v : V → ℝ) (W L : ℝ) (ω : Set E) (a : V)
    (ha : |v a|≤W)
    (hi : (G.cluster (ω∩G.inducedEdges {x | |v x|≤W}) a).Infinite)
    (hbox : (G.cluster (ω∩G.inducedEdges {x | |u x|≤L ∧ |v x|≤W}) a).Finite) :
    ∃ b∈G.cluster (ω∩G.inducedEdges {x | |v x|≤W}) a, L < |u b| := by
  by_contra hn
  push Not at hn
  apply hi
  apply hbox.subset
  rintro b ⟨w⟩
  let w' := w.mapLe (G.openGraph_mono Set.inter_subset_left)
  apply G.walk_reachable_induced _ ω w'
  intro x hx
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
  have hr : x∈G.cluster (ω∩G.inducedEdges {x | |v x|≤W}) a := (w.takeUntil x hx).reachable
  exact ⟨hn x hr,G.cluster_induced_subset ω _ ha hr⟩

lemma strip_cluster_gives_exit (u v : V → ℝ) (A : Set V) (W L D : ℝ)
    (hD : 0≤D) (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hA : ∀ a∈A, |u a|<L ∧ |v a|≤W)
    {ω : Set E} (hi : ∃ a∈A, (G.cluster (ω∩G.inducedEdges {x | |v x|≤W}) a).Infinite)
    (hbox : ∀ a∈A, (G.cluster (ω∩G.inducedEdges {x | |u x|≤L ∧ |v x|≤W}) a).Finite) :
    ω∈G.axisExit u v A L W D true∪G.axisExit u v A L W D false := by
  obtain ⟨a,ha,hi⟩ := hi
  obtain ⟨b,⟨w⟩,hb⟩ := G.infinite_strip_unbounded u v W L ω a (hA a ha).2 hi (hbox a ha)
  apply G.axisExit_of_crossing u v A L W D hD hu ha (hA a ha).1
    (w.mapLe (G.openGraph_mono Set.inter_subset_left)) hb.le
  intro x hx
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
  exact G.cluster_induced_subset ω _ (hA a ha).2 (w.takeUntil x hx).reachable

def stripPercolates (v : V → ℝ) (W : ℝ) : Set (Set E) :=
  {ω | ω∩G.inducedEdges {x | |v x|≤W}∈G.percolates}

def someStripPercolates (v : V → ℝ) : Set (Set E) :=
  ⋃ n : ℕ, G.stripPercolates v n

lemma stripPercolates_measurable [Countable V] [Countable E] (v : V → ℝ) (W : ℝ) :
    MeasurableSet (G.stripPercolates v W) := by
  exact G.measurableSet_percolates.preimage ((BernoulliProduct.measurable_inter_block _).mono (BernoulliProduct.blockSigma_le _) le_rfl)

lemma someStripPercolates_measurable [Countable V] [Countable E] (v : V → ℝ) :
    MeasurableSet (G.someStripPercolates v) :=
  MeasurableSet.iUnion (fun n => G.stripPercolates_measurable v n)

lemma stripPercolates_diff_iff (v : V → ℝ) (W : ℝ) (ω S : Set E) (hS : S.Finite) :
    ω\S∈G.stripPercolates v W ↔ ω∈G.stripPercolates v W := by
  change (ω\S)∩G.inducedEdges {x | |v x|≤W}∈G.percolates ↔ _
  have heq : (ω\S)∩G.inducedEdges {x | |v x|≤W}=
      (ω∩G.inducedEdges {x | |v x|≤W})\S := by ext e; simp only [Set.mem_inter_iff,Set.mem_sdiff]; tauto
  rw [heq]
  exact G.percolates_diff_finite_iff _ S hS

lemma someStripPercolates_zero_one [Countable V] [Countable E]
    (v : V → ℝ) (q : E → unitInterval) :
    BernoulliProduct.law q (G.someStripPercolates v)=0 ∨
      BernoulliProduct.law q (G.someStripPercolates v)=1 := by
  apply BernoulliProduct.zero_one_of_finite_erasure_invariant q _ (G.someStripPercolates_measurable v)
  intro S hS ω
  have heq : BernoulliProduct.forceOn S ∅ ω=ω\S := by
    ext e
    change (if e∈S then False else e∈ω) ↔ e∈ω ∧ e∉S
    split_ifs <;> tauto
  rw [heq]
  simp only [someStripPercolates,Set.mem_iUnion]
  exact exists_congr (fun n => G.stripPercolates_diff_iff v n ω S hS)

def seedStripInfinite (v : V → ℝ) (A : Set V) (W : ℝ) : Set (Set E) :=
  {ω | ∃ a∈A, (G.cluster (ω∩G.inducedEdges {x | |v x|≤W}) a).Infinite}

lemma seedStripInfinite_measurable [Countable V] [Countable E]
    (v : V → ℝ) (A : Set V) (W : ℝ) : MeasurableSet (G.seedStripInfinite v A W) := by
  have hm : Measurable (fun ω : Set E => ω∩G.inducedEdges {x | |v x|≤W}) :=
    (BernoulliProduct.measurable_inter_block _).mono (BernoulliProduct.blockSigma_le _) le_rfl
  have heq : G.seedStripInfinite v A W=⋃ a∈A,
      (fun ω : Set E => ω∩G.inducedEdges {x | |v x|≤W}) ⁻¹' G.infiniteEvent a := by
    ext ω
    simp only [seedStripInfinite,infiniteEvent,Set.mem_ofPred_eq,Set.mem_iUnion,
      Set.mem_preimage,exists_prop]
  rw [heq]
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ =>
    (G.measurableSet_infiniteEvent a).preimage hm

lemma seedStripInfinite_mono (v : V → ℝ) {A B : Set V} (hAB : A⊆B)
    {W U : ℝ} (hWU : W≤U) : G.seedStripInfinite v A W⊆G.seedStripInfinite v B U := by
  rintro ω ⟨a,ha,hi⟩
  exact ⟨a,hAB ha,hi.mono (G.cluster_mono
    (Set.inter_subset_inter_right _ (G.inducedEdges_mono (fun _ hx => hx.trans hWU))) a)⟩

lemma seedStripInfinite_exhaustion (hc : G.fullGraph.Connected) (v : V → ℝ) (o : V) :
    (⋃ n : ℕ, G.seedStripInfinite v (G.vertexBall o n) n)=G.someStripPercolates v := by
  ext ω
  constructor
  · intro h
    obtain ⟨n,a,_ha,hi⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨n,a,hi⟩
  · intro h
    obtain ⟨n,a,hi⟩ := Set.mem_iUnion.mp h
    obtain ⟨r,hr⟩ := G.reachable_mem_vertexBall (hc o a)
    refine Set.mem_iUnion.mpr ⟨max n r,?_⟩
    exact G.seedStripInfinite_mono v (G.vertexBall_mono o (le_max_right n r))
      (by exact_mod_cast le_max_left n r) ⟨a,hr,hi⟩

theorem exists_seed_strip_probability [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (v : V → ℝ) (o : V) (q : E → unitInterval)
    (hpos : 0<BernoulliProduct.law q (G.someStripPercolates v))
    (eps : ℝ) (heps : 0<eps) :
    ∃ m : ℕ, ∃ W : ℝ, 0≤W ∧
      (∀ a∈G.vertexBall o m, |v a|≤W) ∧
      1-eps<(BernoulliProduct.law q).real (G.seedStripInfinite v (G.vertexBall o m) W) := by
  have hone := (G.someStripPercolates_zero_one v q).resolve_left (ne_of_gt hpos)
  let A := fun n : ℕ => G.seedStripInfinite v (G.vertexBall o n) n
  have hmono : Monotone A := fun n r hn => G.seedStripInfinite_mono v
    (G.vertexBall_mono o hn) (Nat.cast_le.mpr hn)
  have ht := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q) hmono
  have heq : (⋃ n, A n)=G.someStripPercolates v := G.seedStripInfinite_exhaustion hc v o
  rw [heq,hone] at ht
  have hreal := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞)≠⊤)).comp ht
  have hnear : ∀ᶠ n in atTop, 1-eps<(BernoulliProduct.law q).real (A n) :=
    hreal.eventually (lt_mem_nhds (by simpa using heps : 1-eps<ENNReal.toReal 1))
  obtain ⟨m,hm⟩ := hnear.exists
  obtain ⟨M,hM⟩ := ((G.vertexBall_finite hl o m).image (fun a => |v a|)).bddAbove
  refine ⟨m,max (m : ℝ) M,?_,?_,?_⟩
  · exact (Nat.cast_nonneg m).trans (le_max_left _ _)
  · intro a ha
    exact (hM (Set.mem_image_of_mem _ ha)).trans (le_max_right _ _)
  · apply hm.trans_le
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (G.seedStripInfinite_mono v (Set.Subset.refl _) (le_max_left _ _))

end CriticalPercolation.BondGraph
end
end
end

end OAI
