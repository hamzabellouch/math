import OAI.Probability.SpanningForest.IntrinsicExhaustion
import OAI.Probability.SpanningForest.GraphDomain
import OAI.Probability.SpanningForest.EdgeAction

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem336.AllPairObservation

def vertexPairs (V : Finset ℕ) : Finset EdgeCode :=
  (V.product V).subtype (fun p => p.1 < p.2)

@[simp] theorem mem_vertexPairs (V : Finset ℕ) (e : EdgeCode) :
    e ∈ vertexPairs V ↔ e.1.1 ∈ V ∧ e.1.2 ∈ V := by
  simp [vertexPairs]

theorem vertexPairs_mono {V W : Finset ℕ} (h : V ⊆ W) :
    vertexPairs V ⊆ vertexPairs W := by
  intro e he
  rw [mem_vertexPairs] at he ⊢
  exact ⟨h he.1, h he.2⟩

def observations (G : GraphCode) (e : EdgeCode) (n : ℕ) : Finset EdgeCode := by
  classical
  exact if h : GraphLocallyFinite G then
    vertexPairs (IntrinsicExhaustion.edgeBallSubgraph G h e n).1 else ∅

@[simp] theorem mem_observations (G : GraphCode) (e a : EdgeCode) (n : ℕ) :
    a ∈ observations G e n ↔ GraphLocallyFinite G ∧
      a.1.1 ∈ IntrinsicExhaustion.edgeBall G e n ∧
      a.1.2 ∈ IntrinsicExhaustion.edgeBall G e n := by
  classical
  by_cases h : GraphLocallyFinite G <;> simp [observations, h]

theorem observations_mono (G : GraphCode) (e : EdgeCode) :
    Monotone (observations G e) := by
  intro n m hnm a ha
  rw [mem_observations] at ha ⊢
  exact ⟨ha.1, IntrinsicExhaustion.edgeBall_mono G e hnm ha.2.1,
    IntrinsicExhaustion.edgeBall_mono G e hnm ha.2.2⟩

theorem self_mem_observations {G : GraphCode} (hG : GraphLocallyFinite G)
    (e : EdgeCode) (n : ℕ) : e ∈ observations G e n := by
  simp [hG]

theorem exists_mem_observations {G : GraphCode} (hc : GraphConnected G)
    (hf : GraphLocallyFinite G) (e a : EdgeCode) :
    ∃ n, a ∈ observations G e n := by
  obtain ⟨n, hn⟩ := IntrinsicExhaustion.GraphConnected.exists_mem_edgeBall hc e a.1.1
  obtain ⟨m, hm⟩ := IntrinsicExhaustion.GraphConnected.exists_mem_edgeBall hc e a.1.2
  refine ⟨max n m, (mem_observations G e a _).mpr ⟨hf, ?_, ?_⟩⟩
  · exact IntrinsicExhaustion.edgeBall_mono G e (le_max_left n m) hn
  · exact IntrinsicExhaustion.edgeBall_mono G e (le_max_right n m) hm

theorem eventually_mem_observations {G : GraphCode} (hc : GraphConnected G)
    (hf : GraphLocallyFinite G) (e a : EdgeCode) :
    ∀ᶠ n in Filter.atTop, a ∈ observations G e n := by
  obtain ⟨n, hn⟩ := exists_mem_observations hc hf e a
  exact Filter.eventually_atTop.mpr ⟨n, fun m hnm => observations_mono G e hnm hn⟩

private theorem measurable_finset_from_membership
    {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSpace β]
    (f : β → Finset α) (hf : ∀ a, MeasurableSet {b | a ∈ f b}) : Measurable f := by
  apply measurable_to_countable
  intro y
  have hpre : f ⁻¹' {f y} = ⋂ a, {b | a ∈ f b ↔ a ∈ f y} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq,
      Finset.ext_iff]
  rw [hpre]
  apply MeasurableSet.iInter
  intro a
  by_cases ha : a ∈ f y
  · simpa only [ha, iff_true] using hf a
  · simpa only [ha, iff_false, Set.compl_ofPred] using (hf a).compl

theorem measurable_observations (e : EdgeCode) (n : ℕ) :
    Measurable (fun G : GraphCode => observations G e n) := by
  apply measurable_finset_from_membership
  intro a
  simpa only [mem_observations, Set.ofPred_and] using
    measurableSet_graphLocallyFinite.inter
      ((IntrinsicExhaustion.measurableSet_mem_edgeBall e a.1.1 n).inter
        (IntrinsicExhaustion.measurableSet_mem_edgeBall e a.1.2 n))

private theorem locallyFinite_relabel {G : GraphCode} (hG : GraphLocallyFinite G)
    (σ : Equiv ℕ ℕ) : GraphLocallyFinite (relabelGraph σ G) := by
  intro u
  apply ((hG (σ.symm u)).image σ).subset
  intro v hv
  exact ⟨σ.symm v, hv, σ.apply_symm_apply v⟩

private theorem locallyFinite_relabel_iff (G : GraphCode) (σ : Equiv ℕ ℕ) :
    GraphLocallyFinite (relabelGraph σ G) ↔ GraphLocallyFinite G := by
  constructor
  · intro h
    have h' := locallyFinite_relabel h σ.symm
    simpa [relabelGraph] using h'
  · exact fun h => locallyFinite_relabel h σ

private theorem endpoints_mapEdge (σ : Equiv ℕ ℕ) (a : EdgeCode) (P : ℕ → Prop) :
    (P (mapEdge σ a).1.1 ∧ P (mapEdge σ a).1.2) ↔
      (P (σ a.1.1) ∧ P (σ a.1.2)) := by
  unfold mapEdge mkEdge
  split_ifs <;> simp only [and_comm]

theorem mem_observations_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (e a : EdgeCode) (n : ℕ) :
    mapEdge σ a ∈ observations (relabelGraph σ G) (mapEdge σ e) n ↔
      a ∈ observations G e n := by
  simp only [mem_observations, locallyFinite_relabel_iff,
    endpoints_mapEdge, IntrinsicExhaustion.mem_edgeBall_relabel]

end Problem336.AllPairObservation

end

end OAI
