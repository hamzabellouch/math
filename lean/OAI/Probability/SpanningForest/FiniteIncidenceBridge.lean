import OAI.Probability.SpanningForest.Definitions
import OAI.Probability.SpanningForest.ReducedLaplacian

namespace OAI

noncomputable section

namespace Problem336.FiniteIncidence

def ValidEdges (V : Finset ℕ) (T : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ T, p.1 ∈ V ∧ p.2 ∈ V ∧ p.1 < p.2

def src (V : Finset ℕ) (T : Finset (ℕ × ℕ)) (h : ValidEdges V T) : T → V :=
  fun e => ⟨e.val.1, (h e.val e.property).1⟩

def dst (V : Finset ℕ) (T : Finset (ℕ × ℕ)) (h : ValidEdges V T) : T → V :=
  fun e => ⟨e.val.2, (h e.val e.property).2.1⟩

theorem ValidEdges.mono {V : Finset ℕ} {S T : Finset (ℕ × ℕ)}
    (h : ValidEdges V T) (hST : S ⊆ T) : ValidEdges V S :=
  fun p hp => h p (hST hp)

def edgeInclusion {S T : Finset (ℕ × ℕ)} (hST : S ⊆ T) : S ↪ T where
  toFun e := ⟨e.val, hST e.property⟩
  inj' := fun _ _ he => Subtype.ext (congrArg (fun e : T => e.val) he)

theorem reducedGradient_submatrix {V : Finset ℕ} {S T : Finset (ℕ × ℕ)}
    (h : ValidEdges V T) (hST : S ⊆ T) (root : V) :
    (ReducedLaplacian.reducedGradient (src V T h) (dst V T h) root).submatrix
      (edgeInclusion hST) id =
      ReducedLaplacian.reducedGradient (src V S (h.mono hST))
        (dst V S (h.mono hST)) root := rfl

theorem edgeAdj_iff_treeAdj (V : Finset ℕ) (T : Finset (ℕ × ℕ))
    (h : ValidEdges V T) (u v : V) :
    ReducedLaplacian.EdgeAdj (src V T h) (dst V T h) u v ↔
      TreeAdj T u.val v.val := by
  constructor
  · rintro ⟨e, he | he⟩
    · have h1 := congrArg Subtype.val he.1
      have h2 := congrArg Subtype.val he.2
      change e.val.1 = u.val at h1
      change e.val.2 = v.val at h2
      change rawPair u.val v.val ∈ T
      rw [← h1, ← h2]
      simp [rawPair, (h e.val e.property).2.2, e.property]
    · have h1 := congrArg Subtype.val he.1
      have h2 := congrArg Subtype.val he.2
      change e.val.1 = v.val at h1
      change e.val.2 = u.val at h2
      change rawPair u.val v.val ∈ T
      rw [← h1, ← h2]
      simp [rawPair, Nat.not_lt_of_ge (le_of_lt (h e.val e.property).2.2), e.property]
  · intro ht
    change rawPair u.val v.val ∈ T at ht
    by_cases huv : u.val < v.val
    · refine ⟨⟨(u.val, v.val), by simpa [rawPair, huv] using ht⟩, Or.inl ?_⟩
      exact ⟨Subtype.ext rfl, Subtype.ext rfl⟩
    · refine ⟨⟨(v.val, u.val), by simpa [rawPair, huv] using ht⟩, Or.inr ?_⟩
      exact ⟨Subtype.ext rfl, Subtype.ext rfl⟩

theorem treeAdj_endpoints_mem {V : Finset ℕ} {T : Finset (ℕ × ℕ)}
    (h : ValidEdges V T) {u v : ℕ} (huv : TreeAdj T u v) :
    u ∈ V ∧ v ∈ V := by
  have hm := h (rawPair u v) huv
  by_cases hlt : u < v
  · simpa [rawPair, hlt] using And.intro hm.1 hm.2.1
  · simpa [rawPair, hlt] using And.intro hm.2.1 hm.1

theorem treePath_endpoint_mem {V : Finset ℕ} {T : Finset (ℕ × ℕ)}
    (h : ValidEdges V T) {u v : ℕ} (hu : u ∈ V)
    (hp : Relation.ReflTransGen (TreeAdj T) u v) : v ∈ V := by
  induction hp with
  | refl => exact hu
  | tail _ hbc _ => exact (treeAdj_endpoints_mem h hbc).2

theorem treePath_lift {V : Finset ℕ} {T : Finset (ℕ × ℕ)}
    (h : ValidEdges V T) {u v : ℕ} (hu : u ∈ V) (hv : v ∈ V)
    (hp : Relation.ReflTransGen (TreeAdj T) u v) :
    Relation.ReflTransGen (ReducedLaplacian.EdgeAdj (src V T h) (dst V T h))
      ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction hp with
  | refl => exact .refl
  | @tail b c hab hbc ih =>
      have hb : b ∈ V := treePath_endpoint_mem h hu hab
      exact (ih hb).tail ((edgeAdj_iff_treeAdj V T h ⟨b, hb⟩ ⟨c, hv⟩).mpr hbc)

theorem connected_iff_treePaths (V : Finset ℕ) (T : Finset (ℕ × ℕ))
    (h : ValidEdges V T) :
    ReducedLaplacian.Connected (src V T h) (dst V T h) ↔
      ∀ u ∈ V, ∀ v ∈ V, Relation.ReflTransGen (TreeAdj T) u v := by
  constructor
  · intro hc u hu v hv
    exact Relation.ReflTransGen.lift Subtype.val
      (fun a b hab => (edgeAdj_iff_treeAdj V T h a b).mp hab) _ _
      (hc ⟨u, hu⟩ ⟨v, hv⟩)
  · intro hc u v
    exact treePath_lift h u.property v.property (hc u.val u.property v.val v.property)

theorem validEdges_of_subgraph {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {T : Finset (ℕ × ℕ)} (hT : T ⊆ K.2) :
    ValidEdges K.1 T := by
  intro p hp
  have h := hK.2.1 p (hT hp)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem treeOn_iff_connected {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {T : Finset (ℕ × ℕ)} (hT : T ⊆ K.2) :
    TreeOn K T ↔ T.card + 1 = K.1.card ∧
      ReducedLaplacian.Connected
        (src K.1 T (validEdges_of_subgraph hK hT))
        (dst K.1 T (validEdges_of_subgraph hK hT)) := by
  rw [connected_iff_treePaths]
  exact ⟨fun ht => ht.2, fun ht => ⟨hT, ht⟩⟩

theorem treeOn_weightedLaplacian_posDef {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {T : Finset (ℕ × ℕ)} (hT : TreeOn K T)
    (root : K.1) (w : T → ℝ) (hw : ∀ e, 0 < w e) :
    (ReducedLaplacian.weightedLaplacian
      (src K.1 T (validEdges_of_subgraph hK hT.1))
      (dst K.1 T (validEdges_of_subgraph hK hT.1)) root w).PosDef :=
  ReducedLaplacian.weightedLaplacian_posDef _ _ root w
    ((treeOn_iff_connected hK hT.1).mp hT).2 hw

def edgeEquivNonroot {V : Finset ℕ} {T : Finset (ℕ × ℕ)}
    (hcard : T.card + 1 = V.card) (root : V) : T ≃ {v : V // v ≠ root} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_coe, Fintype.card_subtype_compl (fun v : V => v = root),
      Fintype.card_coe, Fintype.card_subtype_eq]
    omega)

def treeEdgeEquivNonroot {K : FiniteSubgraphCode} {T : Finset (ℕ × ℕ)}
    (hT : TreeOn K T) (root : K.1) : T ≃ {v : K.1 // v ≠ root} :=
  edgeEquivNonroot hT.2.1 root

def squareReducedGradient (V : Finset ℕ) (T : Finset (ℕ × ℕ))
    (h : ValidEdges V T) (root : V) (e : T ≃ {v : V // v ≠ root}) :
    Matrix {v : V // v ≠ root} {v : V // v ≠ root} ℝ :=
  (ReducedLaplacian.reducedGradient (src V T h) (dst V T h) root).submatrix e.symm id

theorem squareReducedGradient_det_ne_zero (V : Finset ℕ) (T : Finset (ℕ × ℕ))
    (h : ValidEdges V T) (root : V) (e : T ≃ {v : V // v ≠ root})
    (hc : ReducedLaplacian.Connected (src V T h) (dst V T h)) :
    (squareReducedGradient V T h root e).det ≠ 0 := by
  have hinj : Function.Injective (squareReducedGradient V T h root e).mulVec := by
    intro x y hxy
    apply ReducedLaplacian.reducedGradient_mulVec_injective
      (src V T h) (dst V T h) root hc
    funext a
    have he := congrFun hxy (e a)
    simpa [squareReducedGradient, Matrix.mulVec, dotProduct, Matrix.submatrix] using he
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj))

theorem treeOn_squareReducedGradient_det_ne_zero
    {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {T : Finset (ℕ × ℕ)} (hT : TreeOn K T)
    (root : K.1) :
    (squareReducedGradient K.1 T (validEdges_of_subgraph hK hT.1) root
      (treeEdgeEquivNonroot hT root)).det ≠ 0 :=
  squareReducedGradient_det_ne_zero _ _ _ _ _ ((treeOn_iff_connected hK hT.1).mp hT).2

end Problem336.FiniteIncidence

end

end OAI
