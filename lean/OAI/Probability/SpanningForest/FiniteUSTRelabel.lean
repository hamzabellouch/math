import OAI.Probability.SpanningForest.EdgeAction

namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem336

def relabelPair (σ : Equiv ℕ ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  rawPair (σ p.1) (σ p.2)

def relabelEdgeSet (σ : Equiv ℕ ℕ) (T : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  T.image (relabelPair σ)

def relabelFiniteSubgraph (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode) :
    FiniteSubgraphCode :=
  (K.1.image σ, relabelEdgeSet σ K.2)

@[simp] theorem relabelPair_rawPair (σ : Equiv ℕ ℕ) (u v : ℕ) :
    relabelPair σ (rawPair u v) = rawPair (σ u) (σ v) := by
  unfold relabelPair
  by_cases h : u < v
  · rw [rawPair_of_lt h]
  · have hraw : rawPair u v = (v, u) := by simp [rawPair, h]
    rw [hraw]
    exact rawPair_comm _ _

@[simp] theorem relabelPair_edge (σ : Equiv ℕ ℕ) (e : EdgeCode) :
    relabelPair σ e.val = (mapEdge σ e).val := by
  simp [relabelPair, mapEdge]

@[simp] theorem relabelPair_symm (σ : Equiv ℕ ℕ) {p : ℕ × ℕ}
    (hp : p.1 < p.2) :
    relabelPair σ.symm (relabelPair σ p) = p := by
  have h := congrArg Subtype.val (mapEdge_symm_apply σ ⟨p, hp⟩)
  simpa only [← relabelPair_edge] using h

theorem relabelPair_injOn (σ : Equiv ℕ ℕ) :
    Set.InjOn (relabelPair σ) {p : ℕ × ℕ | p.1 < p.2} := by
  intro p hp q hq h
  have h' := congrArg (relabelPair σ.symm) h
  simpa only [relabelPair_symm σ hp, relabelPair_symm σ hq] using h'

theorem relabelEdgeSet_card (σ : Equiv ℕ ℕ) (T : Finset (ℕ × ℕ))
    (hT : ∀ p ∈ T, p.1 < p.2) :
    (relabelEdgeSet σ T).card = T.card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq h
  exact relabelPair_injOn σ (hT p hp) (hT q hq) h

@[simp] theorem relabelEdgeSet_symm (σ : Equiv ℕ ℕ) (T : Finset (ℕ × ℕ))
    (hT : ∀ p ∈ T, p.1 < p.2) :
    relabelEdgeSet σ.symm (relabelEdgeSet σ T) = T := by
  unfold relabelEdgeSet
  rw [Finset.image_image]
  calc
    T.image (fun p => relabelPair σ.symm (relabelPair σ p)) = T.image id := by
      apply Finset.image_congr
      intro p hp
      exact relabelPair_symm σ (hT p hp)
    _ = T := Finset.image_id

theorem relabelEdgeSet_valid (σ : Equiv ℕ ℕ) (T : Finset (ℕ × ℕ))
    (hT : ∀ p ∈ T, p.1 < p.2) :
    ∀ p ∈ relabelEdgeSet σ T, p.1 < p.2 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  have h := (mapEdge σ ⟨q, hT q hq⟩).property
  simpa only [← relabelPair_edge] using h

theorem treeAdj_relabelEdgeSet (σ : Equiv ℕ ℕ) (T : Finset (ℕ × ℕ))
    (hT : ∀ p ∈ T, p.1 < p.2) (u v : ℕ) :
    TreeAdj (relabelEdgeSet σ T) (σ u) (σ v) ↔ TreeAdj T u v := by
  constructor
  · intro h
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
    have hback := congrArg (relabelPair σ.symm) heq
    have hpraw : p = rawPair u v := by
      simpa only [relabelPair_symm σ (hT p hp), relabelPair_rawPair,
        Equiv.symm_apply_apply] using hback
    simpa only [TreeAdj, ← hpraw] using hp
  · intro h
    apply Finset.mem_image.mpr
    exact ⟨rawPair u v, h, relabelPair_rawPair σ u v⟩

theorem treeOn_relabel (σ : Equiv ℕ ℕ) {K : FiniteSubgraphCode}
    (hK : ∀ p ∈ K.2, p.1 < p.2) {T : Finset (ℕ × ℕ)}
    (hT : TreeOn K T) :
    TreeOn (relabelFiniteSubgraph σ K) (relabelEdgeSet σ T) := by
  have hTv : ∀ p ∈ T, p.1 < p.2 := fun p hp => hK p (hT.1 hp)
  refine ⟨Finset.image_subset_image hT.1, ?_, ?_⟩
  · change (relabelEdgeSet σ T).card + 1 = (K.1.image σ).card
    rw [relabelEdgeSet_card σ T hTv, Finset.card_image_of_injective _ σ.injective]
    exact hT.2.1
  · intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    have hpath := hT.2.2 a ha b hb
    clear ha hb hu hv
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      exact ih.tail ((treeAdj_relabelEdgeSet σ T hTv b c).mpr hbc)

@[simp] theorem relabelFiniteSubgraph_symm (σ : Equiv ℕ ℕ)
    (K : FiniteSubgraphCode) (hK : ∀ p ∈ K.2, p.1 < p.2) :
    relabelFiniteSubgraph σ.symm (relabelFiniteSubgraph σ K) = K := by
  apply Prod.ext
  · simp [relabelFiniteSubgraph, Finset.image_image]
  · exact relabelEdgeSet_symm σ K.2 hK

theorem treeOn_relabel_iff (σ : Equiv ℕ ℕ) {K : FiniteSubgraphCode}
    (hK : ∀ p ∈ K.2, p.1 < p.2) {T : Finset (ℕ × ℕ)}
    (hT : ∀ p ∈ T, p.1 < p.2) :
    TreeOn (relabelFiniteSubgraph σ K) (relabelEdgeSet σ T) ↔ TreeOn K T := by
  constructor
  · intro h
    have hback := treeOn_relabel σ.symm (relabelEdgeSet_valid σ K.2 hK) h
    simpa only [relabelFiniteSubgraph_symm σ K hK, relabelEdgeSet_symm σ T hT]
      using hback
  · exact treeOn_relabel σ hK

private theorem treeOn_of_mem_spanningTrees {K : FiniteSubgraphCode}
    {T : Finset (ℕ × ℕ)} (h : T ∈ spanningTrees K) : TreeOn K T := by
  classical
  exact (Finset.mem_filter.mp h).2

private theorem mem_spanningTrees_of_treeOn {K : FiniteSubgraphCode}
    {T : Finset (ℕ × ℕ)} (h : TreeOn K T) : T ∈ spanningTrees K := by
  simp only [spanningTrees, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨h.1, h⟩

theorem spanningTrees_relabel (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) :
    spanningTrees (relabelFiniteSubgraph σ K) =
      (spanningTrees K).image (relabelEdgeSet σ) := by
  ext T
  constructor
  · intro h
    have hT := treeOn_of_mem_spanningTrees h
    have hKv := relabelEdgeSet_valid σ K.2 hK
    have hTv : ∀ p ∈ T, p.1 < p.2 := fun p hp => hKv p (hT.1 hp)
    refine Finset.mem_image.mpr ⟨relabelEdgeSet σ.symm T, ?_, ?_⟩
    · apply mem_spanningTrees_of_treeOn
      have hback := treeOn_relabel σ.symm hKv hT
      simpa only [relabelFiniteSubgraph_symm σ K hK] using hback
    · simpa only [Equiv.symm_symm] using relabelEdgeSet_symm σ.symm T hTv
  · intro h
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp h
    exact mem_spanningTrees_of_treeOn (treeOn_relabel σ hK (treeOn_of_mem_spanningTrees hS))

private theorem relabelEdgeSet_injOn_spanningTrees (σ : Equiv ℕ ℕ)
    (K : FiniteSubgraphCode) (hK : ∀ p ∈ K.2, p.1 < p.2) :
    Set.InjOn (relabelEdgeSet σ) (spanningTrees K) := by
  intro T hT S hS h
  have hTv : ∀ p ∈ T, p.1 < p.2 :=
    fun p hp => hK p ((treeOn_of_mem_spanningTrees hT).1 hp)
  have hSv : ∀ p ∈ S, p.1 < p.2 :=
    fun p hp => hK p ((treeOn_of_mem_spanningTrees hS).1 hp)
  have hback := congrArg (relabelEdgeSet σ.symm) h
  simpa only [relabelEdgeSet_symm σ T hTv, relabelEdgeSet_symm σ S hSv] using hback

theorem spanningTrees_card_relabel (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) :
    (spanningTrees (relabelFiniteSubgraph σ K)).card = (spanningTrees K).card := by
  rw [spanningTrees_relabel σ K hK]
  exact Finset.card_image_iff.mpr (relabelEdgeSet_injOn_spanningTrees σ K hK)

theorem mem_relabelEdgeSet_iff (σ : Equiv ℕ ℕ) (T : Finset (ℕ × ℕ))
    (hT : ∀ p ∈ T, p.1 < p.2) (e : EdgeCode) :
    (mapEdge σ e).val ∈ relabelEdgeSet σ T ↔ e.val ∈ T := by
  simpa only [TreeAdj, mapEdge, mkEdge_val, rawPair_of_lt e.property] using
    treeAdj_relabelEdgeSet σ T hT e.val.1 e.val.2

theorem ustCylinder_relabel (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) (A B : Finset EdgeCode) :
    ustCylinder (relabelFiniteSubgraph σ K)
      (A.image (mapEdge σ)) (B.image (mapEdge σ)) = ustCylinder K A B := by
  classical
  let good := (spanningTrees K).filter (fun T =>
    (∀ e ∈ A, e.val ∈ T) ∧ (∀ e ∈ B, e.val ∉ T))
  have hgood : (spanningTrees (relabelFiniteSubgraph σ K)).filter (fun T =>
      (∀ e ∈ A.image (mapEdge σ), e.val ∈ T) ∧
      (∀ e ∈ B.image (mapEdge σ), e.val ∉ T)) =
      good.image (relabelEdgeSet σ) := by
    rw [spanningTrees_relabel σ K hK]
    ext T
    simp only [good, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨S, hS, rfl⟩, hyes, hno⟩
      have hSv : ∀ p ∈ S, p.1 < p.2 :=
        fun p hp => hK p ((treeOn_of_mem_spanningTrees hS).1 hp)
      refine ⟨S, ⟨hS, ?_⟩, rfl⟩
      constructor
      · intro e he
        exact (mem_relabelEdgeSet_iff σ S hSv e).mp (hyes _ ⟨e, he, rfl⟩)
      · intro e he hin
        exact hno _ ⟨e, he, rfl⟩ ((mem_relabelEdgeSet_iff σ S hSv e).mpr hin)
    · rintro ⟨S, ⟨hS, hyes, hno⟩, rfl⟩
      have hSv : ∀ p ∈ S, p.1 < p.2 :=
        fun p hp => hK p ((treeOn_of_mem_spanningTrees hS).1 hp)
      refine ⟨⟨S, hS, rfl⟩, ?_⟩
      constructor
      · rintro e ⟨a, ha, rfl⟩
        exact (mem_relabelEdgeSet_iff σ S hSv a).mpr (hyes a ha)
      · rintro e ⟨a, ha, rfl⟩ hin
        exact hno a ha ((mem_relabelEdgeSet_iff σ S hSv a).mp hin)
  have hcard : (good.image (relabelEdgeSet σ)).card = good.card := by
    apply Finset.card_image_iff.mpr
    intro T hT S hS h
    change T ∈ good at hT
    change S ∈ good at hS
    simp only [good, Finset.mem_filter] at hT hS
    exact relabelEdgeSet_injOn_spanningTrees σ K hK hT.1 hS.1 h
  unfold ustCylinder
  dsimp only
  rw [hgood, hcard, spanningTrees_card_relabel σ K hK]

theorem IsFiniteConnectedSubgraph.relabel {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) (σ : Equiv ℕ ℕ) :
    IsFiniteConnectedSubgraph (relabelGraph σ G) (relabelFiniteSubgraph σ K) := by
  have hKv : ∀ p ∈ K.2, p.1 < p.2 := fun p hp => (hK.2.1 p hp).2.2.1
  refine ⟨hK.1.image σ, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hqu, hqv, hqlt, hqa⟩ := hK.2.1 q hq
    have hqua : Adj G q.2 q.1 := by
      unfold Adj at *
      rw [G.2.2 q.2 q.1]
      exact hqa
    have hne : σ q.1 ≠ σ q.2 := fun h => Nat.ne_of_lt hqlt (σ.injective h)
    by_cases hlt : σ q.1 < σ q.2
    · simp only [relabelPair, rawPair, hlt, ite_true]
      exact ⟨Finset.mem_image_of_mem σ hqu, Finset.mem_image_of_mem σ hqv,
        True.intro, by simpa [Adj, relabelGraph] using hqa⟩
    · have hgt : σ q.2 < σ q.1 := by omega
      simp only [relabelPair, rawPair, hlt, ite_false]
      exact ⟨Finset.mem_image_of_mem σ hqv, Finset.mem_image_of_mem σ hqu,
        hgt, by simpa [Adj, relabelGraph] using hqua⟩
  · intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    have hpath := hK.2.2 a ha b hb
    clear ha hb hu hv
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      apply ih.tail
      refine ⟨Finset.mem_image_of_mem σ hbc.1,
        Finset.mem_image_of_mem σ hbc.2.1, ?_⟩
      exact (treeAdj_relabelEdgeSet σ K.2 hKv b c).mpr hbc.2.2

theorem IsFiniteConnectedSubgraph.ustCylinder_relabel {G : GraphCode}
    {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K)
    (σ : Equiv ℕ ℕ) (A B : Finset EdgeCode) :
    ustCylinder (relabelFiniteSubgraph σ K)
      (A.image (mapEdge σ)) (B.image (mapEdge σ)) = ustCylinder K A B :=
  Problem336.ustCylinder_relabel σ K (fun p hp => (hK.2.1 p hp).2.2.1) A B

theorem IsConnectedExhaustion.relabel {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H)
    (σ : Equiv ℕ ℕ) :
    IsConnectedExhaustion (relabelGraph σ G)
      (fun n => relabelFiniteSubgraph σ (H n)) := by
  refine ⟨fun n => (hH.1 n).relabel σ, ?_, ?_⟩
  · intro n
    exact ⟨Finset.image_subset_image (hH.2.1 n).1,
      Finset.image_subset_image (hH.2.1 n).2⟩
  · intro u v huv hadj
    have hadj' : Adj G (σ.symm u) (σ.symm v) := hadj
    have hne : σ.symm u ≠ σ.symm v := fun h => Nat.ne_of_lt huv (σ.symm.injective h)
    by_cases hlt : σ.symm u < σ.symm v
    · obtain ⟨n, hn⟩ := hH.2.2 _ _ hlt hadj'
      refine ⟨n, Finset.mem_image.mpr ⟨(σ.symm u, σ.symm v), hn, ?_⟩⟩
      simp [relabelPair, rawPair_of_lt huv]
    · have hgt : σ.symm v < σ.symm u := by omega
      have hadj'' : Adj G (σ.symm v) (σ.symm u) := by
        unfold Adj at *
        rw [G.2.2 (σ.symm v) (σ.symm u)]
        exact hadj'
      obtain ⟨n, hn⟩ := hH.2.2 _ _ hgt hadj''
      refine ⟨n, Finset.mem_image.mpr ⟨(σ.symm v, σ.symm u), hn, ?_⟩⟩
      simp only [relabelPair, Equiv.apply_symm_apply]
      rw [rawPair_comm, rawPair_of_lt huv]

theorem HasFUSFLaw.relabel {Ω : Type} [MeasurableSpace Ω]
    {G : GraphCode} {P : MeasureTheory.Measure Ω} {X : Ω → EdgeConfiguration}
    (hX : HasFUSFLaw G P X) (σ : Equiv ℕ ℕ) :
    HasFUSFLaw (relabelGraph σ G) P
      (fun ω e => X ω (mapEdge σ.symm e)) := by
  refine ⟨fun e => hX.1 (mapEdge σ.symm e), ?_⟩
  intro H hH A B
  have hG : relabelGraph σ.symm (relabelGraph σ G) = G := by
    apply Subtype.ext
    funext u v
    simp [relabelGraph]
  have hHback : IsConnectedExhaustion G
      (fun n => relabelFiniteSubgraph σ.symm (H n)) := by
    simpa only [hG] using hH.relabel σ.symm
  have hlim := hX.2 _ hHback (A.image (mapEdge σ.symm)) (B.image (mapEdge σ.symm))
  have hcyl : (fun n => ustCylinder (relabelFiniteSubgraph σ.symm (H n))
        (A.image (mapEdge σ.symm)) (B.image (mapEdge σ.symm))) =
      (fun n => ustCylinder (H n) A B) := by
    funext n
    exact (hH.1 n).ustCylinder_relabel σ.symm A B
  rw [hcyl] at hlim
  simpa only [Finset.forall_mem_image] using hlim

end Problem336

end

end OAI
