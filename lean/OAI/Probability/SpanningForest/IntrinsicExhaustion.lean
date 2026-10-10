import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

namespace Problem336
namespace IntrinsicExhaustion

def vertexBall (G : GraphCode) (c : ℕ) : ℕ → Set ℕ
  | 0 => {c}
  | n + 1 => vertexBall G c n ∪ {v | ∃ u ∈ vertexBall G c n, Adj G u v}

@[simp] theorem mem_vertexBall_zero (G : GraphCode) (c v : ℕ) :
    v ∈ vertexBall G c 0 ↔ v = c := Iff.rfl

@[simp] theorem mem_vertexBall_succ (G : GraphCode) (c v n : ℕ) :
    v ∈ vertexBall G c (n + 1) ↔
      v ∈ vertexBall G c n ∨ ∃ u ∈ vertexBall G c n, Adj G u v := Iff.rfl

theorem vertexBall_mono (G : GraphCode) (c : ℕ) : Monotone (vertexBall G c) :=
  monotone_nat_of_le_succ (fun _ _ hv => Or.inl hv)

@[simp] theorem center_mem_vertexBall (G : GraphCode) (c n : ℕ) :
    c ∈ vertexBall G c n :=
  vertexBall_mono G c (Nat.zero_le n) rfl

theorem finite_vertexBall {G : GraphCode} (hG : GraphLocallyFinite G)
    (c n : ℕ) : (vertexBall G c n).Finite := by
  induction n with
  | zero => exact Set.finite_singleton c
  | succ n ih =>
    have h := ih.union (ih.biUnion (fun u _ => hG u))
    convert h using 1
    ext v
    simp [vertexBall]

theorem exists_mem_vertexBall_of_reachable {G : GraphCode} {c v : ℕ}
    (h : Relation.ReflTransGen (Adj G) c v) :
    ∃ n, v ∈ vertexBall G c n := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | @tail v w hpath hadj ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, Or.inr ⟨v, hn, hadj⟩⟩

theorem GraphConnected.exists_mem_vertexBall {G : GraphCode}
    (hG : GraphConnected G) (c v : ℕ) :
    ∃ n, v ∈ vertexBall G c n :=
  exists_mem_vertexBall_of_reachable (hG c v)

theorem mem_vertexBall_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (c v n : ℕ) :
    σ v ∈ vertexBall (relabelGraph σ G) (σ c) n ↔ v ∈ vertexBall G c n := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    simp only [mem_vertexBall_succ, ih]
    constructor
    · rintro (hv | ⟨u, hu, huv⟩)
      · exact Or.inl hv
      · right
        refine ⟨σ.symm u, ?_, ?_⟩
        · exact (ih (σ.symm u)).mp (by simpa using hu)
        · simpa [Adj, relabelGraph] using huv
    · rintro (hv | ⟨u, hu, huv⟩)
      · exact Or.inl hv
      · exact Or.inr ⟨σ u, (ih u).mpr hu, by simpa [Adj, relabelGraph] using huv⟩

private theorem measurableSet_ballAdj (u v : ℕ) :
    MeasurableSet {G : GraphCode | Adj G u v} := by
  have hm : Measurable (fun G : GraphCode => G.1 u v) :=
    (measurable_pi_apply v).comp ((measurable_pi_apply u).comp measurable_subtype_coe)
  exact (measurableSet_singleton true).preimage hm

theorem measurableSet_mem_vertexBall (c v n : ℕ) :
    MeasurableSet {G : GraphCode | v ∈ vertexBall G c n} := by
  induction n generalizing v with
  | zero => simp only [mem_vertexBall_zero]; exact MeasurableSet.const _
  | succ n ih =>
    simpa only [mem_vertexBall_succ, Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
      using (ih v).union (MeasurableSet.iUnion (fun u => (ih u).inter (measurableSet_ballAdj u v)))

def edgeBall (G : GraphCode) (e : EdgeCode) (n : ℕ) : Set ℕ :=
  vertexBall G e.1.1 n ∪ vertexBall G e.1.2 n

theorem edgeBall_mono (G : GraphCode) (e : EdgeCode) : Monotone (edgeBall G e) := by
  intro n m hnm v hv
  exact hv.elim (fun h => Or.inl (vertexBall_mono G e.1.1 hnm h))
    (fun h => Or.inr (vertexBall_mono G e.1.2 hnm h))

theorem finite_edgeBall {G : GraphCode} (hG : GraphLocallyFinite G)
    (e : EdgeCode) (n : ℕ) : (edgeBall G e n).Finite :=
  (finite_vertexBall hG e.1.1 n).union (finite_vertexBall hG e.1.2 n)

@[simp] theorem fst_mem_edgeBall (G : GraphCode) (e : EdgeCode) (n : ℕ) :
    e.1.1 ∈ edgeBall G e n := Or.inl (center_mem_vertexBall G e.1.1 n)

@[simp] theorem snd_mem_edgeBall (G : GraphCode) (e : EdgeCode) (n : ℕ) :
    e.1.2 ∈ edgeBall G e n := Or.inr (center_mem_vertexBall G e.1.2 n)

theorem GraphConnected.exists_mem_edgeBall {G : GraphCode}
    (hG : GraphConnected G) (e : EdgeCode) (v : ℕ) :
    ∃ n, v ∈ edgeBall G e n := by
  obtain ⟨n, hn⟩ := GraphConnected.exists_mem_vertexBall hG e.1.1 v
  exact ⟨n, Or.inl hn⟩

theorem mem_edgeBall_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (e : EdgeCode) (v n : ℕ) :
    σ v ∈ edgeBall (relabelGraph σ G) (mapEdge σ e) n ↔ v ∈ edgeBall G e n := by
  unfold edgeBall mapEdge mkEdge
  split_ifs <;> simp only [Set.mem_union, mem_vertexBall_relabel, or_comm]

theorem measurableSet_mem_edgeBall (e : EdgeCode) (v n : ℕ) :
    MeasurableSet {G : GraphCode | v ∈ edgeBall G e n} :=
  (measurableSet_mem_vertexBall e.1.1 v n).union
    (measurableSet_mem_vertexBall e.1.2 v n)

theorem vertexBall_reachable {G : GraphCode} {c v n : ℕ}
    (hv : v ∈ vertexBall G c n) :
    Relation.ReflTransGen
      (fun x y => x ∈ vertexBall G c n ∧ y ∈ vertexBall G c n ∧ Adj G x y) c v := by
  induction n generalizing v with
  | zero =>
    have : v = c := hv
    subst v
    exact .refl
  | succ n ih =>
    have hlift : ∀ {v}, v ∈ vertexBall G c n →
        Relation.ReflTransGen
          (fun x y => x ∈ vertexBall G c (n + 1) ∧
            y ∈ vertexBall G c (n + 1) ∧ Adj G x y) c v := by
      intro v hv
      apply Relation.ReflTransGen.mono (fun x y h =>
        ⟨Or.inl h.1, Or.inl h.2.1, h.2.2⟩) _ _ (ih hv)
    rcases hv with hv | ⟨u, hu, huv⟩
    · exact hlift hv
    · exact (hlift hu).tail ⟨Or.inl hu, Or.inr ⟨u, hu, huv⟩, huv⟩

theorem edgeBall_reachable {G : GraphCode} {e : EdgeCode} {v n : ℕ}
    (he : Adj G e.1.1 e.1.2) (hv : v ∈ edgeBall G e n) :
    Relation.ReflTransGen
      (fun x y => x ∈ edgeBall G e n ∧ y ∈ edgeBall G e n ∧ Adj G x y) e.1.1 v := by
  rcases hv with hv | hv
  · exact Relation.ReflTransGen.mono
      (fun x y h => ⟨Or.inl h.1, Or.inl h.2.1, h.2.2⟩) _ _ (vertexBall_reachable hv)
  · exact (Relation.ReflTransGen.single
      ⟨fst_mem_edgeBall G e n, snd_mem_edgeBall G e n, he⟩).trans
        (Relation.ReflTransGen.mono
          (fun x y h => ⟨Or.inr h.1, Or.inr h.2.1, h.2.2⟩) _ _ (vertexBall_reachable hv))

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
  ballInducedSubgraph G (finite_edgeBall hG e n).toFinset

@[simp] theorem mem_edgeBallSubgraph_vertices (G : GraphCode)
    (hG : GraphLocallyFinite G) (e : EdgeCode) (n v : ℕ) :
    v ∈ (edgeBallSubgraph G hG e n).1 ↔ v ∈ edgeBall G e n := by
  simp [edgeBallSubgraph]

@[simp] theorem subgraphAdj_edgeBallSubgraph (G : GraphCode)
    (hG : GraphLocallyFinite G) (e : EdgeCode) (n u v : ℕ) :
    SubgraphAdj (edgeBallSubgraph G hG e n) u v ↔
      u ∈ edgeBall G e n ∧ v ∈ edgeBall G e n ∧ Adj G u v := by
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
      p.1 ∈ edgeBall G e n ∧ p.2 ∈ edgeBall G e n ∧ p.1 < p.2 ∧ Adj G p.1 p.2 := by
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
    obtain ⟨m, hm⟩ := GraphConnected.exists_mem_edgeBall hC e u
    obtain ⟨n, hn⟩ := GraphConnected.exists_mem_edgeBall hC e v
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
      (measurableSet_mem_edgeBall e v n).preimage measurable_subtype_coe
  have hE : Measurable (fun G : {G : GraphCode // GraphLocallyFinite G} =>
      (edgeBallSubgraph G.1 G.2 e n).2) := by
    apply measurable_finset_from_membership
    intro p
    by_cases hp : p.1 < p.2
    · have h := ((measurableSet_mem_edgeBall e p.1 n).inter
        ((measurableSet_mem_edgeBall e p.2 n).inter
          (measurableSet_ballAdj p.1 p.2))).preimage
            (measurable_subtype_coe : Measurable
              (fun G : {G : GraphCode // GraphLocallyFinite G} => G.1))
      simpa only [mem_edgeBallSubgraph_edges, hp, true_and, Set.preimage_inter,
        Set.preimage_ofPred_eq, Set.ofPred_and] using h
    · simp only [mem_edgeBallSubgraph_edges, hp, false_and, and_false, Set.ofPred_false,
        MeasurableSet.empty]
  exact hV.prodMk hE

end IntrinsicExhaustion
end Problem336

end

end OAI
