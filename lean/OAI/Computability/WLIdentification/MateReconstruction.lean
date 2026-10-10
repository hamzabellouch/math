import OAI.Computability.WLIdentification.AffineIncidence

namespace OAI

namespace WLIdentification

theorem histogram_eq_of_equiv {α β γ : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → γ) (g : β → γ) (h : ∀ a, f a = g (e a)) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  rw [← Multiset.map_univ_val_equiv e, Multiset.map_map]
  exact Multiset.map_congr rfl (fun a _ => h a)

theorem filteredHistogram_eq_of_equiv {α β γ : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q]
    (f : α → γ) (g : β → γ) (hp : ∀ a, p a ↔ q (e a)) (h : ∀ a, f a = g (e a)) :
    (Finset.univ.filter p).val.map f = (Finset.univ.filter q).val.map g := by
  simp only [Finset.filter_val]
  conv_rhs => rw [← Multiset.map_univ_val_equiv e, Multiset.filter_map, Multiset.map_map]
  apply Multiset.map_congr
  · exact Multiset.filter_congr (fun a _ => hp a)
  · exact fun a _ => h a

theorem isomorphic_refl (G : Graph) : Isomorphic G G := ⟨Equiv.refl _, fun _ _ => rfl⟩

theorem isomorphic_symm {G H : Graph} (h : Isomorphic G H) : Isomorphic H G := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  intro v w
  simpa only [e.apply_symm_apply] using (he (e.symm v) (e.symm w)).symm

theorem isomorphic_trans {G H I : Graph} (h : Isomorphic G H) (h' : Isomorphic H I) :
    Isomorphic G I := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := h'
  exact ⟨e.trans f, fun v w => (he v w).trans (hf (e v) (e w))⟩

theorem neighborColor_isomorphic {G H : Graph} (e : Fin G.order ≃ Fin H.order)
    (he : ∀ v w, G.edge v w = H.edge (e v) (e w)) (s : ℕ) (v : Fin G.order) :
    neighborColor G s v = neighborColor H s (e v) := by
  induction s generalizing v with
  | zero => rfl
  | succ s ih =>
    change (neighborColor G s v, _) = (neighborColor H s (e v), _)
    apply Prod.ext (ih v)
    exact filteredHistogram_eq_of_equiv e _ _ _ _
      (fun w => by rw [he v w]) ih

theorem tupleColor_isomorphic {G H : Graph} (e : Fin G.order ≃ Fin H.order)
    (he : ∀ v w, G.edge v w = H.edge (e v) (e w)) (k s : ℕ) (v : Fin k → Fin G.order) :
    tupleColor G k s v = tupleColor H k s (e ∘ v) := by
  induction s generalizing v with
  | zero =>
    apply Prod.ext
    · funext i j
      exact decide_eq_decide.mpr e.injective.eq_iff.symm
    · funext i j
      exact he (v i) (v j)
  | succ s ih =>
    change (tupleColor G k s v, _) = (tupleColor H k s (e ∘ v), _)
    apply Prod.ext (ih v)
    apply histogram_eq_of_equiv e
    intro z
    funext i
    simpa only [Function.comp_update] using ih (Function.update v i z)

theorem isomorphic_equivalent {G H : Graph} (h : Isomorphic G H) (k : ℕ) : Equivalent k G H := by
  obtain ⟨e, he⟩ := h
  unfold Equivalent
  split_ifs
  · intro s
    exact histogram_eq_of_equiv e _ _ (neighborColor_isomorphic e he s)
  · intro s
    exact histogram_eq_of_equiv (Equiv.piCongrRight (fun _ : Fin k => e)) _ _
      (tupleColor_isomorphic e he k s)

theorem equivalent_trans {G H I : Graph} {k : ℕ}
    (h : Equivalent k G H) (h' : Equivalent k H I) : Equivalent k G I := by
  unfold Equivalent at *
  split_ifs at * <;> exact fun s => (h s).trans (h' s)

def simpleOfGraph (G : Graph) : SimpleGraph (Fin G.order) where
  Adj v w := G.edge v w = true
  symm := ⟨by intro v w; rw [G.symmetric v w]; exact id⟩
  loopless := ⟨by intro v; rw [G.loopless v]; decide⟩

instance simpleOfGraph_decidable (G : Graph) : DecidableRel (simpleOfGraph G).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

theorem graph_simple_isomorphic (G : Graph) : Isomorphic G (graphOfSimple (simpleOfGraph G)) := by
  refine ⟨Fintype.equivFin (Fin G.order), ?_⟩
  intro v w
  have hh : decide ((simpleOfGraph G).Adj v w) = G.edge v w := by
    cases h : G.edge v w <;> simp [simpleOfGraph, h]
  exact hh.symm.trans (graphOfSimple_edge (simpleOfGraph G) v w).symm

@[simp]
theorem simpleOfGraph_degree (G : Graph) (v : Fin G.order) :
    (simpleOfGraph G).degree v = degree G v := by
  unfold SimpleGraph.degree degree
  congr 1
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- A degree-one vertex has the same unique neighbor in every incident edge. -/
theorem degree_one_neighbors_eq {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v x y : V} (hd : G.degree v = 1)
    (hx : G.Adj v x) (hy : G.Adj v y) : x = y := by
  obtain ⟨w, _, hw⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd
  exact (hw x hx).trans (hw y hy).symm

/-- Private-leaf reconstruction by exact finite counting. The prescribed leaf
counts exhaust all leaf vertices; no separate leaf-only component can remain. -/
theorem private_leaf_reconstruction {V : Type} [Fintype V] (ell : V → ℕ)
    (H : SimpleGraph (LeafVertex ell)) [DecidableRel H.Adj]
    (hleaf : ∀ (v : V) (j : Fin (ell v)), H.degree (.inr ⟨v, j⟩) = 1)
    (hcount : ∀ v, Fintype.card {l : Σ v, Fin (ell v) // H.Adj (.inl v) (.inr l)} = ell v) :
    ∃ e : withLeaves (H.comap Sum.inl) ell ≃g H, ∀ v, e (.inl v) = .inl v := by
  classical
  let F (v : V) : Fin (ell v) ≃ {l : Σ v, Fin (ell v) // H.Adj (.inl v) (.inr l)} :=
    Classical.choice (Fintype.card_eq.mp (by rw [Fintype.card_fin, hcount]))
  let f : (Σ v, Fin (ell v)) → (Σ v, Fin (ell v)) := fun l => (F l.1 l.2).val
  have hfadj (l : Σ v, Fin (ell v)) : H.Adj (.inl l.1) (.inr (f l)) := (F l.1 l.2).property
  have hfparent (l : Σ v, Fin (ell v)) (v : V) :
      H.Adj (.inl v) (.inr (f l)) ↔ v = l.1 := by
    constructor
    · intro h
      exact Sum.inl.inj (degree_one_neighbors_eq H (hleaf (f l).1 (f l).2)
        h.symm (hfadj l).symm)
    · rintro rfl
      exact hfadj l
  have hfinj : Function.Injective f := by
    intro l m heq
    have hp : l.1 = m.1 := (hfparent m l.1).mp (heq ▸ hfadj l)
    obtain ⟨v, i⟩ := l
    obtain ⟨w, j⟩ := m
    dsimp at hp
    subst w
    have hij : i = j := (F v).injective (Subtype.ext heq)
    subst j
    rfl
  let E := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, rfl⟩)
  refine ⟨{ toEquiv := Equiv.sumCongr (Equiv.refl V) E, map_rel_iff' := ?_ }, fun _ => rfl⟩
  intro x y
  cases x with
  | inl v =>
    cases y with
    | inl w => rfl
    | inr l => exact hfparent l v
  | inr l =>
    cases y with
    | inl v =>
      change H.Adj (.inr (f l)) (.inl v) ↔ l.1 = v
      rw [H.adj_comm, hfparent, eq_comm]
    | inr m =>
      change H.Adj (.inr (f l)) (.inr (f m)) ↔ False
      refine ⟨fun h => ?_, False.elim⟩
      have hf := degree_one_neighbors_eq H (hleaf (f l).1 (f l).2) h (hfadj l).symm
      cases hf

def simpleDegreeNeighbors {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w ∧ G.degree w = d)).card

@[simp]
theorem graphOfSimple_degree_at {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (i : Fin (Fintype.card V)) :
    degree (graphOfSimple G) i = G.degree ((Fintype.equivFin V).symm i) := by
  have hh := graphOfSimple_degree G ((Fintype.equivFin V).symm i)
  simpa only [Equiv.apply_symm_apply] using hh

@[simp]
theorem graphOfSimple_degreeNeighbors {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (d : ℕ) :
    degreeNeighbors (graphOfSimple G) (Fintype.equivFin V v) d = simpleDegreeNeighbors G v d := by
  classical
  unfold degreeNeighbors simpleDegreeNeighbors
  apply Finset.card_equiv (Fintype.equivFin V).symm
  intro j
  have hdegree := graphOfSimple_degree_at G j
  simp only [graphOfSimple] at hdegree ⊢
  simp [hdegree]
  intro _ _
  exact Finset.mem_univ _

/-- Transfer the literal WL local information to any finite graph vertex types. -/
theorem simple_equivalent_local {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {k m : ℕ} (hk : 2 ≤ k) (h : Equivalent k (graphOfSimple G) (graphOfSimple H))
    (hm : m ≤ k) (hm0 : 0 < m) (v : Fin m → V) :
    ∃ w : Fin m → W,
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ i j, G.Adj (v i) (v j) ↔ H.Adj (w i) (w j)) ∧
      (∀ i, G.degree (v i) = H.degree (w i)) ∧
      (∀ i d, simpleDegreeNeighbors G (v i) d = simpleDegreeNeighbors H (w i) d) := by
  classical
  obtain ⟨wg, heq, hadj, hd, hn⟩ := equivalent_local_neighborhood_match hk h hm hm0
    (fun i => Fintype.equivFin V (v i))
  let w (i : Fin m) : W := (Fintype.equivFin W).symm (wg i)
  have hw (i : Fin m) : Fintype.equivFin W (w i) = wg i := Equiv.apply_symm_apply _ _
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact (Fintype.equivFin V).injective.eq_iff.symm.trans
      ((heq i j).trans (Fintype.equivFin W).symm.injective.eq_iff.symm)
  · intro i j
    have hh := hadj i j
    rw [← hw i, ← hw j] at hh
    have hv := graphOfSimple_edge G (v i) (v j)
    have hw' := graphOfSimple_edge H (w i) (w j)
    exact decide_eq_decide.mp (hv.symm.trans (hh.trans hw'))
  · intro i
    have hh := hd i
    rw [← hw i] at hh
    exact (graphOfSimple_degree G (v i)).symm.trans (hh.trans (graphOfSimple_degree H (w i)))
  · intro i d
    have hh := hn i d
    rw [← hw i] at hh
    exact (graphOfSimple_degreeNeighbors G (v i) d).symm.trans
      (hh.trans (graphOfSimple_degreeNeighbors H (w i) d))

theorem simple_equivalent_local_finite {A V W : Type}
    [Fintype A] [Nonempty A] [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {k : ℕ} (hk : 2 ≤ k) (h : Equivalent k (graphOfSimple G) (graphOfSimple H))
    (hA : Fintype.card A ≤ k) (v : A → V) :
    ∃ w : A → W,
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ i j, G.Adj (v i) (v j) ↔ H.Adj (w i) (w j)) ∧
      (∀ i, G.degree (v i) = H.degree (w i)) ∧
      (∀ i d, simpleDegreeNeighbors G (v i) d = simpleDegreeNeighbors H (w i) d) := by
  obtain ⟨w, heq, hadj, hd, hn⟩ := simple_equivalent_local G H hk h hA
    Fintype.card_pos (fun i => v ((Fintype.equivFin A).symm i))
  refine ⟨w ∘ Fintype.equivFin A, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using heq (Fintype.equivFin A i) (Fintype.equivFin A j)
  · intro i j
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hadj (Fintype.equivFin A i) (Fintype.equivFin A j)
  · intro i
    have hv := congrArg (fun a => G.degree (v a)) ((Fintype.equivFin A).symm_apply_apply i)
    exact hv.symm.trans (hd (Fintype.equivFin A i))
  · intro i d
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hn (Fintype.equivFin A i) d

/-- The diagonal-tuple degree bijection is independent of the chosen finite encoding. -/
theorem simple_equivalent_degreeBijection {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {k : ℕ} (hk : 2 ≤ k) (h : Equivalent k (graphOfSimple G) (graphOfSimple H)) :
    ∃ e : V ≃ W, ∀ v, G.degree v = H.degree (e v) := by
  obtain ⟨e, he⟩ := equivalent_degreeBijection hk h
  let E := (Fintype.equivFin V).trans (e.trans (Fintype.equivFin W).symm)
  refine ⟨E, ?_⟩
  intro v
  have hh := he (Fintype.equivFin V v)
  exact (graphOfSimple_degree G v).symm.trans (hh.trans (graphOfSimple_degree_at H _))

theorem leaf_count_eq_degreeNeighbors {V : Type} [Fintype V] (ell : V → ℕ)
    (H : SimpleGraph (LeafVertex ell)) [DecidableRel H.Adj]
    (hleaf : ∀ (v : V) (j : Fin (ell v)), H.degree (.inr ⟨v, j⟩) = 1)
    (hbase : ∀ v, 1 < H.degree (.inl v)) (v : V) :
    Fintype.card {l : Σ v, Fin (ell v) // H.Adj (.inl v) (.inr l)} =
      simpleDegreeNeighbors H (.inl v) 1 := by
  classical
  let e : {l : Σ v, Fin (ell v) // H.Adj (.inl v) (.inr l)} ≃
      {x : LeafVertex ell // H.Adj (.inl v) x ∧ H.degree x = 1} := {
    toFun l := ⟨.inr l.val, l.property, hleaf l.val.1 l.val.2⟩
    invFun x := by
      rcases x with ⟨x, hx, hd⟩
      cases x with
      | inl w => exact False.elim (by have := hbase w; omega)
      | inr l => exact ⟨l, hx⟩
    left_inv _ := rfl
    right_inv x := by
      rcases x with ⟨x, hx, hd⟩
      cases x with
      | inl w => exact False.elim (by have := hbase w; omega)
      | inr l => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  rfl

theorem tagged_degreeNeighbors_one {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (color : V → ℕ) (hc : ∀ v, 0 < color v) (v : V) :
    simpleDegreeNeighbors (withLeaves G (tagSize color)) (.inl v) 1 = tagSize color v := by
  classical
  rw [← leaf_count_eq_degreeNeighbors _ _ (withLeaves_leaf_degree G _) (tag_base_degree_gt_one G color hc)]
  let e : {l : Σ v, Fin (tagSize color v) // (withLeaves G (tagSize color)).Adj (.inl v) (.inr l)} ≃
      Fin (tagSize color v) := {
    toFun l := by
      have hl : v = l.val.1 := l.property
      exact hl.symm ▸ l.val.2
    invFun i := ⟨⟨v, i⟩, rfl⟩
    left_inv l := by
      rcases l with ⟨⟨w, i⟩, hw⟩
      change v = w at hw
      subst w
      rfl
    right_inv _ := rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

/-- An arbitrary WL mate of a leaf-coded graph has exactly the same leaf-coded
shape. This theorem quantifies over all finite mate graphs, with no gadget promise. -/
theorem tagged_arbitrary_mate {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (color : V → ℕ) (hc : ∀ v, 0 < color v) {k : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k (taggedGraph G color) (graphOfSimple H)) :
    ∃ G' : SimpleGraph V, Nonempty (withLeaves G' (tagSize color) ≃g H) := by
  classical
  let T := withLeaves G (tagSize color)
  obtain ⟨e, he⟩ := simple_equivalent_degreeBijection T H hk h
  let H' := H.comap e
  let E : H' ≃g H := SimpleGraph.Iso.comap e H
  have hd (v : LeafVertex (tagSize color)) : H'.degree v = T.degree v :=
    (E.degree_eq v).symm.trans (he v).symm
  have hleaf (v : V) (i : Fin (tagSize color v)) : H'.degree (.inr ⟨v, i⟩) = 1 := by
    rw [hd, withLeaves_leaf_degree]
  have hbase (v : V) : 1 < H'.degree (.inl v) := by
    rw [hd]
    exact tag_base_degree_gt_one G color hc v
  have heq : Equivalent k (graphOfSimple H') (graphOfSimple T) :=
    equivalent_trans (isomorphic_equivalent ((isomorphic_graphOfSimple_iff H' H).mpr ⟨E⟩) k)
      (equivalent_symm h)
  have hn (v : V) : simpleDegreeNeighbors H' (.inl v) 1 = tagSize color v := by
    obtain ⟨w, _, _, hw, hneigh⟩ := simple_equivalent_local H' T hk heq
      (m := 1) (by omega) (by omega) (fun _ => .inl v)
    have hdeg := hw 0
    have hh := hneigh 0 1
    cases hval : w 0 with
    | inr l =>
      rw [hval, withLeaves_leaf_degree] at hdeg
      have := hbase v
      omega
    | inl u =>
      rw [hval] at hdeg hh
      have hcu : color v = color u := by
        rw [hd] at hdeg
        have hdiv := congrArg (fun n => n / (Fintype.card V + 1)) hdeg
        simpa only [T, tag_degree_color] using hdiv
      rw [tagged_degreeNeighbors_one G color hc] at hh
      exact hh.trans (by simp only [tagSize, hcu])
  have hn' (v : V) : Fintype.card {l : Σ v, Fin (tagSize color v) // H'.Adj (.inl v) (.inr l)} =
      tagSize color v := (leaf_count_eq_degreeNeighbors _ H' hleaf hbase v).trans (hn v)
  obtain ⟨F, _⟩ := private_leaf_reconstruction (tagSize color) H' hleaf hn'
  exact ⟨H'.comap Sum.inl, ⟨F.trans E⟩⟩

/-- A bounded set of base vertices of equivalent tagged graphs has a simultaneous
color-preserving induced-graph match. Degree coding recovers the original colors. -/
theorem tagged_equivalent_local {A V W : Type} [Fintype A] [Nonempty A]
    [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (color : V → ℕ) (color' : W → ℕ)
    (hc : ∀ v, 0 < color v)
    (hN : Fintype.card V = Fintype.card W) {k : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k (taggedGraph G color) (taggedGraph H color'))
    (hA : Fintype.card A ≤ k) (v : A → V) :
    ∃ w : A → W, (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ i j, G.Adj (v i) (v j) ↔ H.Adj (w i) (w j)) ∧
      (∀ i, color (v i) = color' (w i)) := by
  classical
  obtain ⟨w, he, ha, hd, _⟩ := simple_equivalent_local_finite
    (withLeaves G (tagSize color)) (withLeaves H (tagSize color')) hk h hA (fun i => .inl (v i))
  have hw (i : A) : ∃ u, w i = .inl u := by
    cases hh : w i with
    | inl u => exact ⟨u, rfl⟩
    | inr l =>
      have hd' := hd i
      rw [hh, withLeaves_leaf_degree] at hd'
      have := tag_base_degree_gt_one G color hc (v i)
      omega
  choose w' hw' using hw
  refine ⟨w', ?_, ?_, ?_⟩
  · intro i j
    simpa only [hw', Sum.inl.injEq] using he i j
  · intro i j
    simpa only [hw', withLeaves] using ha i j
  · intro i
    have hh := hd i
    rw [hw'] at hh
    have hdiv := congrArg (fun n => n / (Fintype.card V + 1)) hh
    rw [tag_degree_color, hN, tag_degree_color] at hdiv
    exact hdiv

namespace AffineBlocks

variable {C B : Type} [Fintype C] [DecidableEq C]

def AllowedName (D : AffineBlocks C B) (x y : C ⊕ B) : Prop :=
  match x, y with
  | .inl c, .inr b => c ∈ D.coordinates b
  | .inr b, .inl c => c ∈ D.coordinates b
  | _, _ => False

theorem allowed_name (D : AffineBlocks C B) {beta : B → Bit} (x y : D.Vertex beta) :
    D.Allowed x y ↔ D.AllowedName (D.colorName x) (D.colorName y) := by
  cases x <;> cases y <;> rfl

theorem piece_contains_color (D : AffineBlocks C B) {beta : B → Bit} (b : B)
    (x : D.Piece beta b) (y : D.Vertex beta)
    (h : D.colorName y = D.colorName (D.pieceEmbed b x)) :
    ∃ y' : D.Piece beta b, D.pieceEmbed b y' = y := by
  cases x with
  | inl p =>
    obtain ⟨a, ha⟩ := D.exists_bit_of_color y p.1.val h
    exact ⟨.inl (p.1, a), ha.symm⟩
  | inr v =>
    obtain ⟨u, hu⟩ := D.exists_valuation_of_color y b h
    exact ⟨.inr u, hu.symm⟩

variable [Fintype B]

/-- Bounded local WL information excludes every edge between forbidden colors. -/
theorem tagged_equivalent_allowed (D : AffineBlocks C B) (H : SimpleGraph (D.Vertex 0))
    [DecidableRel H.Adj] {k : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k (D.graph 0) (taggedGraph H D.colorNat)) :
    ∀ x y, H.Adj x y → D.Allowed x y := by
  classical
  intro x y hxy
  obtain ⟨w, _, ha, hc⟩ := tagged_equivalent_local (A := Fin 2) H (D.baseGraph 0)
    D.colorNat D.colorNat D.colorNat_pos rfl hk (equivalent_symm h)
    (by simpa using hk) ![x, y]
  have he : (D.baseGraph 0).Adj (w 0) (w 1) := (ha 0 1).mp hxy
  have hcx := (D.colorNat_eq_iff _ _).mp (hc 0)
  have hcy := (D.colorNat_eq_iff _ _).mp (hc 1)
  change D.colorName x = D.colorName (w 0) at hcx
  change D.colorName y = D.colorName (w 1) at hcy
  have hallow := D.base_adj_allowed he
  rw [D.allowed_name] at hallow ⊢
  rw [hcx, hcy]
  exact hallow

/-- Match a complete incidence piece at once. Finite cardinality upgrades the
injective local match into an isomorphism of the entire piece. -/
theorem tagged_equivalent_piece (D : AffineBlocks C B) (H : SimpleGraph (D.Vertex 0))
    [DecidableRel H.Adj] {k : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k (D.graph 0) (taggedGraph H D.colorNat)) (b : B)
    (hb : Fintype.card (D.Piece 0 b) ≤ k) :
    ∃ e : D.pieceGraph 0 b ≃g H.comap (D.pieceEmbed b),
      ∀ v, D.colorName (D.pieceEmbed b (e v)) = D.colorName (D.pieceEmbed b v) := by
  classical
  let : Nonempty (D.Piece 0 b) := ⟨.inr ⟨0, D.legal_zero b⟩⟩
  obtain ⟨w, he, ha, hc⟩ := tagged_equivalent_local (A := D.Piece 0 b) (D.baseGraph 0) H
    D.colorNat D.colorNat D.colorNat_pos rfl hk h hb (D.pieceEmbed b)
  have hw (x : D.Piece 0 b) : ∃ y : D.Piece 0 b, D.pieceEmbed b y = w x :=
    D.piece_contains_color b x (w x) ((D.colorNat_eq_iff _ _).mp (hc x)).symm
  choose f hf using hw
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply (D.pieceEmbed b).injective
    apply (he x y).mpr
    rw [← hf x, ← hf y, hxy]
  let E := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, rfl⟩)
  refine ⟨{ toEquiv := E, map_rel_iff' := ?_ }, ?_⟩
  · intro x y
    change H.Adj (D.pieceEmbed b (f x)) (D.pieceEmbed b (f y)) ↔
      (D.baseGraph 0).Adj (D.pieceEmbed b x) (D.pieceEmbed b y)
    rw [hf, hf]
    exact (ha x y).symm
  · intro x
    change D.colorName (D.pieceEmbed b (f x)) = _
    rw [hf]
    exact ((D.colorNat_eq_iff _ _).mp (hc x)).symm

/-- Full arbitrary-mate reconstruction, not pair-equivalence hardness: every
finite uncolored WL mate is isomorphic to some affine shift of the same system. -/
theorem graph_arbitrary_mate (D : AffineBlocks C B) {k : ℕ} (hk : 2 ≤ k)
    (hbound : ∀ b, Fintype.card (D.Piece 0 b) ≤ k) (H : Graph)
    (h : Equivalent k (D.graph 0) H) :
    ∃ beta : B → Bit, Isomorphic H (D.graph beta) := by
  classical
  have hS : Equivalent k (D.graph 0) (graphOfSimple (simpleOfGraph H)) :=
    equivalent_trans h (isomorphic_equivalent (graph_simple_isomorphic H) k)
  obtain ⟨H0, ⟨E⟩⟩ := tagged_arbitrary_mate (D.baseGraph 0) (simpleOfGraph H)
    D.colorNat D.colorNat_pos hk hS
  have hE := (isomorphic_graphOfSimple_iff _ _).mpr ⟨E⟩
  have h0 : Equivalent k (D.graph 0) (taggedGraph H0 D.colorNat) :=
    equivalent_trans hS (isomorphic_equivalent (isomorphic_symm hE) k)
  obtain ⟨beta, F, hF⟩ := D.base_reconstruction H0
    (D.tagged_equivalent_allowed H0 hk h0)
    (fun b => D.tagged_equivalent_piece H0 hk h0 b (hbound b))
  have hsize (v : D.Vertex beta) : tagSize D.colorNat v = tagSize D.colorNat (F v) := by
    dsimp only [tagSize]
    rw [D.vertex_card beta 0]
    exact congrArg (fun n => n * (Fintype.card (D.Vertex 0) + 1))
      ((D.colorNat_eq_iff _ _).mpr (hF v).symm)
  let T := withLeavesIso F (tagSize D.colorNat) (tagSize D.colorNat) hsize
  have hT : Isomorphic (D.graph beta) (taggedGraph H0 D.colorNat) :=
    (isomorphic_graphOfSimple_iff _ _).mpr ⟨T⟩
  refine ⟨beta, isomorphic_symm ?_⟩
  exact isomorphic_trans hT (isomorphic_trans hE (isomorphic_symm (graph_simple_isomorphic H)))

end AffineBlocks

end WLIdentification

end OAI
