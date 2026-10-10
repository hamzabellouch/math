import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336.BorelFiniteChoice

theorem exists_measurable_selector {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable β] [Nonempty β] (P : α → β → Prop)
    (hP : ∀ b, MeasurableSet {a | P a b}) (hex : ∀ a, ∃ b, P a b) :
    ∃ f : α → β, Measurable f ∧ ∀ a, P a (f a) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat β
  have hn : ∀ a, ∃ n, P a (e n) := by
    intro a
    obtain ⟨b, hb⟩ := hex a
    obtain ⟨n, rfl⟩ := he b
    exact ⟨n, hb⟩
  refine ⟨fun a => e (Nat.find (hn a)), ?_, fun a => Nat.find_spec (hn a)⟩
  exact (measurable_of_countable e).comp (measurable_find hn (fun n => hP (e n)))

theorem exists_measurable_partial_selector {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable β] [Nonempty β]
    (P : α → β → Prop) (hP : ∀ b, MeasurableSet {a | P a b}) :
    ∃ f : α → β, Measurable f ∧ ∀ a, (∃ b, P a b) → P a (f a) := by
  classical
  have hexm : MeasurableSet {a | ∃ b, P a b} := by
    have := MeasurableSet.iUnion hP
    convert this using 1
    ext a
    simp
  obtain ⟨f, hf, hfw⟩ := exists_measurable_selector
    (fun a b => P a b ∨ ¬∃ c, P a c)
    (fun b => (hP b).union hexm.compl) (by
      intro a
      by_cases h : ∃ b, P a b
      · obtain ⟨b, hb⟩ := h
        exact ⟨b, Or.inl hb⟩
      · exact ⟨Classical.choice inferInstance, Or.inr h⟩)
  exact ⟨f, hf, fun a ha => (hfw a).resolve_right (not_not_intro ha)⟩

lemma measurableSet_adj (u v : ℕ) : MeasurableSet {G : GraphCode | Adj G u v} := by
  exact measurableSet_eq_fun
    ((measurable_pi_apply v).comp ((measurable_pi_apply u).comp measurable_subtype_coe))
    measurable_const

lemma measurableSet_finiteConnected (K : FiniteSubgraphCode) :
    MeasurableSet {G : GraphCode | IsFiniteConnectedSubgraph G K} := by
  classical
  have hadj (u v : ℕ) : Measurable (fun G : GraphCode => Adj G u v) :=
    measurableSet_setOfPred.mp (measurableSet_adj u v)
  unfold IsFiniteConnectedSubgraph
  measurability

theorem exists_measurable_connected_extension :
    ∃ f : GraphCode × FiniteSubgraphCode → FiniteSubgraphCode,
      Measurable f ∧ ∀ G K₀,
        (∃ K, IsFiniteConnectedSubgraph G K ∧ K₀.1 ⊆ K.1 ∧ K₀.2 ⊆ K.2) →
        IsFiniteConnectedSubgraph G (f (G, K₀)) ∧
          K₀.1 ⊆ (f (G, K₀)).1 ∧ K₀.2 ⊆ (f (G, K₀)).2 := by
  have hpred (K : FiniteSubgraphCode) :
      MeasurableSet {q : GraphCode × FiniteSubgraphCode |
        IsFiniteConnectedSubgraph q.1 K ∧ q.2.1 ⊆ K.1 ∧ q.2.2 ⊆ K.2} := by
    apply measurableSet_setOfPred.mpr
    apply measurable_from_prod_countable_left
    intro K₀
    change Measurable (fun G : GraphCode =>
      IsFiniteConnectedSubgraph G K ∧ K₀.1 ⊆ K.1 ∧ K₀.2 ⊆ K.2)
    exact (measurableSet_setOfPred.mp (measurableSet_finiteConnected K)).and
      (measurable_const : Measurable (fun _ : GraphCode => K₀.1 ⊆ K.1 ∧ K₀.2 ⊆ K.2))
  obtain ⟨f, hf, hfw⟩ := exists_measurable_partial_selector
    (fun q : GraphCode × FiniteSubgraphCode => fun K =>
      IsFiniteConnectedSubgraph q.1 K ∧ q.2.1 ⊆ K.1 ∧ q.2.2 ⊆ K.2) hpred
  exact ⟨f, hf, fun G K₀ => hfw (G, K₀)⟩

end Problem336.BorelFiniteChoice

end

end OAI
