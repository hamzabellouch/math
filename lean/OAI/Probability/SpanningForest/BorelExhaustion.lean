import OAI.Probability.SpanningForest.BorelFiniteChoice
import OAI.Probability.SpanningForest.ExhaustionExistence

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336.BorelExhaustion

def edgeWindow (G : GraphCode) (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
    (fun p => p.1 < p.2 ∧ Adj G p.1 p.2)

lemma mem_edgeWindow (G : GraphCode) (n : ℕ) (p : ℕ × ℕ) :
    p ∈ edgeWindow G n ↔ p.1 < n + 1 ∧ p.2 < n + 1 ∧ p.1 < p.2 ∧ Adj G p.1 p.2 := by
  rcases p with ⟨u, v⟩
  simp [edgeWindow, and_assoc]

lemma measurable_edgeWindow (n : ℕ) : Measurable (fun G => edgeWindow G n) := by
  rw [measurable_finset_iff]
  intro p
  simp only [mem_edgeWindow]
  exact measurable_const.and (measurable_const.and
    (measurable_const.and (measurableSet_setOfPred.mp (BorelFiniteChoice.measurableSet_adj p.1 p.2))))

def extensionChoice : GraphCode × FiniteSubgraphCode → FiniteSubgraphCode :=
  Classical.choose BorelFiniteChoice.exists_measurable_connected_extension

lemma measurable_extensionChoice : Measurable extensionChoice :=
  (Classical.choose_spec BorelFiniteChoice.exists_measurable_connected_extension).1

lemma extensionChoice_spec (G : GraphCode) (K₀ : FiniteSubgraphCode)
    (h : ∃ K, IsFiniteConnectedSubgraph G K ∧ K₀.1 ⊆ K.1 ∧ K₀.2 ⊆ K.2) :
    IsFiniteConnectedSubgraph G (extensionChoice (G, K₀)) ∧
      K₀.1 ⊆ (extensionChoice (G, K₀)).1 ∧ K₀.2 ⊆ (extensionChoice (G, K₀)).2 :=
  (Classical.choose_spec BorelFiniteChoice.exists_measurable_connected_extension).2 G K₀ h

def requirements (G : GraphCode) (n : ℕ) (K : FiniteSubgraphCode) : FiniteSubgraphCode :=
  (K.1 ∪ Finset.range (n + 1), K.2 ∪ edgeWindow G n)

lemma measurable_requirements (n : ℕ) :
    Measurable (fun q : GraphCode × FiniteSubgraphCode => requirements q.1 n q.2) := by
  apply measurable_from_prod_countable_left
  intro K
  change Measurable (fun G : GraphCode =>
    (K.1 ∪ Finset.range (n + 1), K.2 ∪ edgeWindow G n))
  exact measurable_const.prodMk
    ((measurable_of_countable (fun E : Finset (ℕ × ℕ) => K.2 ∪ E)).comp
      (measurable_edgeWindow n))

def candidate (G : GraphCode) : ℕ → FiniteSubgraphCode
  | 0 => extensionChoice (G, requirements G 0 (∅, ∅))
  | n + 1 => extensionChoice (G, requirements G (n + 1) (candidate G n))

lemma measurable_candidate (n : ℕ) : Measurable (fun G => candidate G n) := by
  induction n with
  | zero =>
    exact measurable_extensionChoice.comp (measurable_id.prodMk
      ((measurable_requirements 0).comp (measurable_id.prodMk measurable_const)))
  | succ n ih =>
    exact measurable_extensionChoice.comp (measurable_id.prodMk
      ((measurable_requirements (n + 1)).comp (measurable_id.prodMk ih)))

lemma measurable_candidate_sequence : Measurable candidate :=
  Measurable.of_eval measurable_candidate

def ExtensionProperty (G : GraphCode) : Prop :=
  ∀ K₀ : FiniteSubgraphCode,
    (∀ p ∈ K₀.2, p.1 < p.2 ∧ Adj G p.1 p.2) →
    ∃ K, IsFiniteConnectedSubgraph G K ∧ K₀.1 ⊆ K.1 ∧ K₀.2 ⊆ K.2

lemma step_spec (G : GraphCode) (hExt : ExtensionProperty G)
    (n : ℕ) (K : FiniteSubgraphCode)
    (hedges : ∀ p ∈ K.2, p.1 < p.2 ∧ Adj G p.1 p.2) :
    IsFiniteConnectedSubgraph G (extensionChoice (G, requirements G n K)) ∧
      (requirements G n K).1 ⊆ (extensionChoice (G, requirements G n K)).1 ∧
      (requirements G n K).2 ⊆ (extensionChoice (G, requirements G n K)).2 := by
  apply extensionChoice_spec
  apply hExt
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact hedges p hp
  · exact (mem_edgeWindow G n p).mp hp |>.2.2

lemma candidate_spec (G : GraphCode) (hExt : ExtensionProperty G) (n : ℕ) :
    IsFiniteConnectedSubgraph G (candidate G n) ∧
      Finset.range (n + 1) ⊆ (candidate G n).1 ∧
      edgeWindow G n ⊆ (candidate G n).2 := by
  induction n with
  | zero =>
    have hs := step_spec G hExt 0 (∅, ∅) (by simp)
    exact ⟨hs.1, Finset.subset_union_right.trans hs.2.1,
      Finset.subset_union_right.trans hs.2.2⟩
  | succ n ih =>
    have hs := step_spec G hExt (n + 1) (candidate G n)
      (fun p hp => (ih.1.2.1 p hp).2.2)
    exact ⟨hs.1, Finset.subset_union_right.trans hs.2.1,
      Finset.subset_union_right.trans hs.2.2⟩

lemma candidate_isConnectedExhaustion (G : GraphCode) (hExt : ExtensionProperty G) :
    IsConnectedExhaustion G (candidate G) := by
  refine ⟨fun n => (candidate_spec G hExt n).1, ?_, ?_⟩
  · intro n
    have hs := step_spec G hExt (n + 1) (candidate G n)
      (fun p hp => ((candidate_spec G hExt n).1.2.1 p hp).2.2)
    exact ⟨Finset.subset_union_left.trans hs.2.1, Finset.subset_union_left.trans hs.2.2⟩
  · intro u v huv hadj
    refine ⟨v, (candidate_spec G hExt v).2.2 ?_⟩
    exact (mem_edgeWindow G v (u, v)).mpr ⟨by omega, by omega, huv, hadj⟩

lemma extensionProperty_of_graphConnected {G : GraphCode} (hG : GraphConnected G) :
    ExtensionProperty G :=
  hG.exists_finiteConnected_extension

theorem candidate_isConnectedExhaustion_of_connected {G : GraphCode}
    (hG : GraphConnected G) : IsConnectedExhaustion G (candidate G) :=
  candidate_isConnectedExhaustion G (extensionProperty_of_graphConnected hG)

theorem exists_measurable_connected_exhaustion :
    ∃ H : GraphCode → ℕ → FiniteSubgraphCode, Measurable H ∧
      ∀ G, GraphConnected G → IsConnectedExhaustion G (H G) :=
  ⟨candidate, measurable_candidate_sequence,
    fun _ hG => candidate_isConnectedExhaustion_of_connected hG⟩

lemma subgraphAdj_implies_adj {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {u v : ℕ} (h : SubgraphAdj K u v) :
    Adj G u v := by
  have hp := h.2.2
  unfold rawPair at hp
  by_cases huv : u < v
  · have hm : (u, v) ∈ K.2 := by simpa [huv] using hp
    exact (hK.2.1 (u, v) hm).2.2.2
  · have hm : (v, u) ∈ K.2 := by simpa [huv] using hp
    have ha := (hK.2.1 (v, u) hm).2.2.2
    unfold Adj at *
    rwa [G.2.2 u v]

lemma graphConnected_iff_finiteConnected_pairs (G : GraphCode) :
    GraphConnected G ↔ ∀ u v : ℕ, ∃ K : FiniteSubgraphCode,
      IsFiniteConnectedSubgraph G K ∧ u ∈ K.1 ∧ v ∈ K.1 := by
  constructor
  · intro hG u v
    obtain ⟨K, hK, hsub⟩ := hG.exists_finiteConnected_containing {u, v}
    exact ⟨K, hK, hsub (by simp), hsub (by simp)⟩
  · intro h u v
    obtain ⟨K, hK, hu, hv⟩ := h u v
    exact Relation.ReflTransGen.mono
      (fun _ _ hadj => subgraphAdj_implies_adj hK hadj) u v (hK.2.2 u hu v hv)

lemma measurableSet_graphConnected : MeasurableSet {G : GraphCode | GraphConnected G} := by
  have hm : Measurable (fun G : GraphCode => ∀ u v : ℕ, ∃ K : FiniteSubgraphCode,
      IsFiniteConnectedSubgraph G K ∧ u ∈ K.1 ∧ v ∈ K.1) := by
    apply Measurable.forall
    intro u
    apply Measurable.forall
    intro v
    apply Measurable.exists
    intro K
    exact (measurableSet_setOfPred.mp (BorelFiniteChoice.measurableSet_finiteConnected K)).and
      (measurable_const : Measurable (fun _ : GraphCode => u ∈ K.1 ∧ v ∈ K.1))
  convert measurableSet_setOfPred.mpr hm using 1
  ext G
  exact graphConnected_iff_finiteConnected_pairs G

end Problem336.BorelExhaustion

end

end OAI
