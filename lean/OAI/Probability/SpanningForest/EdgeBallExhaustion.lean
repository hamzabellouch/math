import OAI.Probability.SpanningForest.GraphBalls

namespace OAI

noncomputable section

namespace Problem336

@[simp] theorem fst_mem_edgeBall (G : GraphCode) (e : EdgeCode) (n : ℕ) :
    e.1.1 ∈ edgeBall G n e := Or.inl (withinRadius_refl G n e.1.1)

@[simp] theorem snd_mem_edgeBall (G : GraphCode) (e : EdgeCode) (n : ℕ) :
    e.1.2 ∈ edgeBall G n e := Or.inr (withinRadius_refl G n e.1.2)

theorem withinRadius_reachable_inside {G : GraphCode} {c v n : ℕ}
    (hv : withinRadius G n c v) :
    Relation.ReflTransGen
      (fun x y => withinRadius G n c x ∧ withinRadius G n c y ∧ Adj G x y) c v := by
  induction n generalizing v with
  | zero =>
    have : c = v := hv
    subst v
    exact .refl
  | succ n ih =>
    have hlift : ∀ {v}, withinRadius G n c v →
        Relation.ReflTransGen
          (fun x y => withinRadius G (n + 1) c x ∧
            withinRadius G (n + 1) c y ∧ Adj G x y) c v := by
      intro v hv
      exact Relation.ReflTransGen.mono (fun x y h =>
        ⟨Or.inl h.1, Or.inl h.2.1, h.2.2⟩) _ _ (ih hv)
    rcases hv with hv | ⟨u, hu, huv⟩
    · exact hlift hv
    · exact (hlift hu).tail ⟨Or.inl hu, Or.inr ⟨u, hu, huv⟩, huv⟩

theorem edgeBall_reachable {G : GraphCode} {e : EdgeCode} {v n : ℕ}
    (he : Adj G e.1.1 e.1.2) (hv : v ∈ edgeBall G n e) :
    Relation.ReflTransGen
      (fun x y => x ∈ edgeBall G n e ∧ y ∈ edgeBall G n e ∧ Adj G x y) e.1.1 v := by
  rcases hv with hv | hv
  · exact Relation.ReflTransGen.mono
      (fun x y h => ⟨Or.inl h.1, Or.inl h.2.1, h.2.2⟩) _ _ (withinRadius_reachable_inside hv)
  · exact (Relation.ReflTransGen.single
      ⟨fst_mem_edgeBall G e n, snd_mem_edgeBall G e n, he⟩).trans
        (Relation.ReflTransGen.mono
          (fun x y h => ⟨Or.inr h.1, Or.inr h.2.1, h.2.2⟩) _ _ (withinRadius_reachable_inside hv))

def ballInducedSubgraph (G : GraphCode) (s : Finset ℕ) : FiniteSubgraphCode := by
  classical
  exact (s, (s.product s).filter (fun p => p.1 < p.2 ∧ Adj G p.1 p.2))

@[simp] theorem ballInducedSubgraph_vertices (G : GraphCode) (s : Finset ℕ) :
    (ballInducedSubgraph G s).1 = s := rfl

@[simp] theorem mem_ballInducedSubgraph_edges (G : GraphCode) (s : Finset ℕ)
    (p : ℕ × ℕ) :
    p ∈ (ballInducedSubgraph G s).2 ↔
      p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2 ∧ Adj G p.1 p.2 := by
  classical
  simp [ballInducedSubgraph, and_assoc]

private theorem ballAdj_symm {G : GraphCode} {u v : ℕ} (h : Adj G u v) : Adj G v u :=
  (G.2.2 v u).trans h

private theorem ballAdj_ne {G : GraphCode} {u v : ℕ} (h : Adj G u v) : u ≠ v := by
  rintro rfl
  have hfalse := G.2.1 u
  simp [Adj, hfalse] at h

@[simp] theorem rawPair_mem_ballInducedSubgraph (G : GraphCode) (s : Finset ℕ)
    (u v : ℕ) :
    rawPair u v ∈ (ballInducedSubgraph G s).2 ↔ u ∈ s ∧ v ∈ s ∧ Adj G u v := by
  by_cases huv : u < v
  · simp [rawPair, huv]
  · simp only [rawPair, ite_eq_right huv, mem_ballInducedSubgraph_edges]
    constructor
    · rintro ⟨hv, hu, _, hAdj⟩
      exact ⟨hu, hv, ballAdj_symm hAdj⟩
    · rintro ⟨hu, hv, hAdj⟩
      exact ⟨hv, hu, lt_of_le_of_ne (Nat.le_of_not_gt huv) (Ne.symm (ballAdj_ne hAdj)),
        ballAdj_symm hAdj⟩

@[simp] theorem subgraphAdj_ballInducedSubgraph (G : GraphCode) (s : Finset ℕ)
    (u v : ℕ) :
    SubgraphAdj (ballInducedSubgraph G s) u v ↔ u ∈ s ∧ v ∈ s ∧ Adj G u v := by
  simp only [SubgraphAdj, ballInducedSubgraph_vertices, rawPair_mem_ballInducedSubgraph]
  tauto

def edgeBallSubgraph (G : GraphCode) (hG : GraphLocallyFinite G)
    (e : EdgeCode) (n : ℕ) : FiniteSubgraphCode :=
  ballInducedSubgraph G (finite_edgeBall G hG n e).toFinset

@[simp] theorem mem_edgeBallSubgraph_vertices (G : GraphCode)
    (hG : GraphLocallyFinite G) (e : EdgeCode) (n v : ℕ) :
    v ∈ (edgeBallSubgraph G hG e n).1 ↔ v ∈ edgeBall G n e := by
  simp [edgeBallSubgraph]

@[simp] theorem subgraphAdj_edgeBallSubgraph (G : GraphCode)
    (hG : GraphLocallyFinite G) (e : EdgeCode) (n u v : ℕ) :
    SubgraphAdj (edgeBallSubgraph G hG e n) u v ↔
      u ∈ edgeBall G n e ∧ v ∈ edgeBall G n e ∧ Adj G u v := by
  simp [edgeBallSubgraph]

theorem isFiniteConnectedSubgraph_edgeBallSubgraph {G : GraphCode}
    (hG : GraphLocallyFinite G) (e : EdgeCode) (he : Adj G e.1.1 e.1.2) (n : ℕ) :
    IsFiniteConnectedSubgraph G (edgeBallSubgraph G hG e n) := by
  refine ⟨⟨e.1.1, by simp⟩, ?_, ?_⟩
  · intro p hp
    simpa [edgeBallSubgraph] using hp
  · intro u hu v hv
    have path (w : ℕ) (hw : w ∈ (edgeBallSubgraph G hG e n).1) :
        Relation.ReflTransGen (SubgraphAdj (edgeBallSubgraph G hG e n)) e.1.1 w := by
      apply Relation.ReflTransGen.mono (fun x y hxy =>
        (subgraphAdj_edgeBallSubgraph G hG e n x y).mpr hxy) _ _
        (edgeBall_reachable he ((mem_edgeBallSubgraph_vertices G hG e n w).mp hw))
    let : Std.Symm (SubgraphAdj (edgeBallSubgraph G hG e n)) := ⟨fun x y hxy => by
      rw [subgraphAdj_edgeBallSubgraph] at hxy ⊢
      exact ⟨hxy.2.1, hxy.1, ballAdj_symm hxy.2.2⟩⟩
    exact (symm (path u hu)).trans (path v hv)

@[simp] theorem mem_edgeBallSubgraph_edges (G : GraphCode)
    (hG : GraphLocallyFinite G) (e : EdgeCode) (n : ℕ) (p : ℕ × ℕ) :
    p ∈ (edgeBallSubgraph G hG e n).2 ↔
      p.1 ∈ edgeBall G n e ∧ p.2 ∈ edgeBall G n e ∧ p.1 < p.2 ∧ Adj G p.1 p.2 := by
  simp [edgeBallSubgraph]

theorem isConnectedExhaustion_edgeBallSubgraph {G : GraphCode}
    (hC : GraphConnected G) (hL : GraphLocallyFinite G)
    (e : EdgeCode) (he : Adj G e.1.1 e.1.2) :
    IsConnectedExhaustion G (edgeBallSubgraph G hL e) := by
  refine ⟨isFiniteConnectedSubgraph_edgeBallSubgraph hL e he, ?_, ?_⟩
  · intro n
    constructor
    · intro v hv
      rw [mem_edgeBallSubgraph_vertices] at hv ⊢
      exact edgeBall_mono G e (Nat.le_succ n) hv
    · intro p hp
      rw [mem_edgeBallSubgraph_edges] at hp ⊢
      exact ⟨edgeBall_mono G e (Nat.le_succ n) hp.1,
        edgeBall_mono G e (Nat.le_succ n) hp.2.1, hp.2.2⟩
  · intro u v huv hAdj
    obtain ⟨m, hm⟩ := exists_mem_edgeBall G hC e u
    obtain ⟨n, hn⟩ := exists_mem_edgeBall G hC e v
    refine ⟨max m n, ?_⟩
    rw [mem_edgeBallSubgraph_edges]
    exact ⟨edgeBall_mono G e (le_max_left m n) hm,
      edgeBall_mono G e (le_max_right m n) hn, huv, hAdj⟩

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

theorem measurable_edgeBallSubgraph (e : EdgeCode) (n : ℕ) :
    Measurable (fun G : {G : GraphCode // GraphLocallyFinite G} =>
      edgeBallSubgraph G.1 G.2 e n) := by
  have hV : Measurable (fun G : {G : GraphCode // GraphLocallyFinite G} =>
      (edgeBallSubgraph G.1 G.2 e n).1) := by
    apply measurable_finset_from_membership
    intro v
    simpa only [mem_edgeBallSubgraph_vertices, Set.preimage_ofPred_eq] using
      (measurableSet_mem_edgeBall n v e).preimage measurable_subtype_coe
  have hE : Measurable (fun G : {G : GraphCode // GraphLocallyFinite G} =>
      (edgeBallSubgraph G.1 G.2 e n).2) := by
    apply measurable_finset_from_membership
    intro p
    by_cases hp : p.1 < p.2
    · have h := ((measurableSet_mem_edgeBall n p.1 e).inter
        ((measurableSet_mem_edgeBall n p.2 e).inter
          (measurableSet_adj p.1 p.2))).preimage
            (measurable_subtype_coe : Measurable
              (fun G : {G : GraphCode // GraphLocallyFinite G} => G.1))
      simpa only [mem_edgeBallSubgraph_edges, hp, true_and, Set.preimage_inter,
        Set.preimage_ofPred_eq, Set.ofPred_and] using h
    · simp only [mem_edgeBallSubgraph_edges, hp, false_and, and_false, Set.ofPred_false,
        MeasurableSet.empty]
  exact hV.prodMk hE

end Problem336

end

end OAI
