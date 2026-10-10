import OAI.Computability.WLIdentification.Refinement

namespace OAI

namespace WLIdentification

noncomputable def graphOfSimple {V : Type} [Fintype V] (G : SimpleGraph V) : Graph := by
  classical
  exact {
    order := Fintype.card V
    edge := fun i j => decide (G.Adj ((Fintype.equivFin V).symm i) ((Fintype.equivFin V).symm j))
    symmetric := fun i j => by simp only [G.adj_comm]
    loopless := fun i => by simp }

@[simp]
theorem graphOfSimple_edge {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v w : V) :
    (graphOfSimple G).edge (Fintype.equivFin V v) (Fintype.equivFin V w) =
      decide (G.Adj v w) := by
  classical
  simp [graphOfSimple]

@[simp]
theorem graphOfSimple_degree {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    degree (graphOfSimple G) (Fintype.equivFin V v) = G.degree v := by
  classical
  unfold degree SimpleGraph.degree
  apply Finset.card_equiv (Fintype.equivFin V).symm
  intro j
  simp only [graphOfSimple]
  simp
  intro _
  exact Finset.mem_univ _

abbrev LeafVertex {V : Type} (ell : V → ℕ) := V ⊕ (Σ v, Fin (ell v))

def withLeaves {V : Type} (G : SimpleGraph V) (ell : V → ℕ) : SimpleGraph (LeafVertex ell) where
  Adj x y := match x, y with
    | .inl v, .inl w => G.Adj v w
    | .inl v, .inr w => v = w.1
    | .inr v, .inl w => v.1 = w
    | .inr _, .inr _ => False
  symm := ⟨by
    intro x y
    cases x <;> cases y <;> first | exact G.adj_symm | exact Eq.symm | exact id⟩
  loopless := ⟨by
    intro x
    cases x <;> simp⟩

noncomputable instance withLeaves_decidable {V : Type} (G : SimpleGraph V) (ell : V → ℕ) :
    DecidableRel (withLeaves G ell).Adj := Classical.decRel _

def baseNeighborEquiv {V : Type} (G : SimpleGraph V) (ell : V → ℕ) (v : V) :
    (withLeaves G ell).neighborSet (.inl v) ≃ G.neighborSet v ⊕ Fin (ell v) where
  toFun x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | inl w => exact .inl ⟨w, hx⟩
    | inr w =>
      obtain ⟨w, j⟩ := w
      have h : v = w := hx
      subst w
      exact .inr j
  invFun x := match x with
    | .inl w => ⟨.inl w.val, w.property⟩
    | .inr j => ⟨.inr ⟨v, j⟩, rfl⟩
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | inl w => rfl
    | inr w =>
      obtain ⟨w, j⟩ := w
      have h : v = w := hx
      subst w
      rfl
  right_inv x := by cases x <;> rfl

@[simp]
theorem withLeaves_base_degree {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ell : V → ℕ) (v : V) :
    (withLeaves G ell).degree (.inl v) = G.degree v + ell v := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    Fintype.card_congr (baseNeighborEquiv G ell v), Fintype.card_sum,
    Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree]

@[simp]
theorem withLeaves_leaf_degree {V : Type} [Fintype V] (G : SimpleGraph V)
    (ell : V → ℕ) (v : V) (j : Fin (ell v)) :
    (withLeaves G ell).degree (.inr ⟨v, j⟩) = 1 := by
  classical
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  refine ⟨.inl v, rfl, ?_⟩
  intro y hy
  cases y with
  | inl w => exact congrArg Sum.inl (Eq.symm hy)
  | inr _ => exact False.elim hy

def tagSize {V : Type} [Fintype V] (color : V → ℕ) (v : V) : ℕ :=
  color v * (Fintype.card V + 1)

noncomputable def taggedGraph {V : Type} [Fintype V] (G : SimpleGraph V) (color : V → ℕ) : Graph :=
  graphOfSimple (withLeaves G (tagSize color))

/-- The color is recovered literally by the indicated disjoint degree intervals. -/
theorem tag_degree_color {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (color : V → ℕ) (v : V) :
    (withLeaves G (tagSize color)).degree (.inl v) / (Fintype.card V + 1) = color v := by
  rw [withLeaves_base_degree, tagSize, Nat.add_mul_div_right _ _ (by omega)]
  have hlt := G.degree_lt_card_verts v
  rw [Nat.div_eq_of_lt (by omega : G.degree v < Fintype.card V + 1)]
  omega

theorem tag_base_degree_gt_one {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (color : V → ℕ) (hcolor : ∀ v, 0 < color v) (v : V) :
    1 < (withLeaves G (tagSize color)).degree (.inl v) := by
  rw [withLeaves_base_degree, tagSize]
  have hN := Fintype.card_pos_iff.mpr ⟨v⟩
  have hj := hcolor v
  nlinarith

/-- Color-preserving base isomorphisms extend to all private leaves. -/
def withLeavesIso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (ell : V → ℕ) (ell' : W → ℕ) (hell : ∀ v, ell v = ell' (e v)) :
    withLeaves G ell ≃g withLeaves H ell' where
  toEquiv := Equiv.sumCongr e.toEquiv (Equiv.sigmaCongr e.toEquiv (fun v => finCongr (hell v)))
  map_rel_iff' := by
    intro x y
    cases x <;> cases y
    · exact e.map_adj_iff
    · change e _ = e _ ↔ _ = _
      exact e.toEquiv.injective.eq_iff
    · change e _ = e _ ↔ _ = _
      exact e.toEquiv.injective.eq_iff
    · rfl

noncomputable def baseDegreeEquiv {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (color : V → ℕ) (hcolor : ∀ v, 0 < color v) :
    V ≃ {x : LeafVertex (tagSize color) // 1 < (withLeaves G (tagSize color)).degree x} where
  toFun v := ⟨.inl v, tag_base_degree_gt_one G color hcolor v⟩
  invFun x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | inl v => exact v
    | inr w =>
      have hf := withLeaves_leaf_degree G (tagSize color) w.1 w.2
      exact False.elim (by rw [hf] at hx; omega)
  left_inv _ := rfl
  right_inv x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | inl v => rfl
    | inr w =>
      have hf := withLeaves_leaf_degree G (tagSize color) w.1 w.2
      exact False.elim (by rw [hf] at hx; omega)

/-- The leaf gadget really erases colors: uncolored isomorphism forces one
color-preserving base isomorphism, not a separate choice in each block. -/
theorem taggedIso_iff {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (color : V → ℕ) (color' : W → ℕ)
    (hc : ∀ v, 0 < color v) (hc' : ∀ w, 0 < color' w)
    (hN : Fintype.card V = Fintype.card W) :
    Nonempty (withLeaves G (tagSize color) ≃g withLeaves H (tagSize color')) ↔
      ∃ e : G ≃g H, ∀ v, color v = color' (e v) := by
  constructor
  · rintro ⟨e⟩
    let E := e.toEquiv.subtypeEquiv
      (p := fun x => 1 < (withLeaves G (tagSize color)).degree x)
      (q := fun x => 1 < (withLeaves H (tagSize color')).degree x)
      (fun x => by
        change (1 < (withLeaves G (tagSize color)).degree x) ↔
          (1 < (withLeaves H (tagSize color')).degree (e x))
        rw [e.degree_eq])
    let e0 := (baseDegreeEquiv G color hc).trans (E.trans (baseDegreeEquiv H color' hc').symm)
    have he0 (v : V) : Sum.inl (e0 v) = e (Sum.inl v) := by
      have hh := congrArg Subtype.val ((baseDegreeEquiv H color' hc').apply_symm_apply
        (E (baseDegreeEquiv G color hc v)))
      exact hh
    let e1 : G ≃g H := {
      toEquiv := e0
      map_rel_iff' := by
        intro v w
        have hh := e.map_adj_iff (v := Sum.inl v) (w := Sum.inl w)
        rw [← he0 v, ← he0 w] at hh
        exact hh }
    refine ⟨e1, ?_⟩
    intro v
    have hd := e.degree_eq (Sum.inl v)
    rw [← he0 v] at hd
    have hdiv := congrArg (fun n => n / (Fintype.card V + 1)) hd
    rw [tag_degree_color, hN, tag_degree_color] at hdiv
    exact hdiv.symm
  · rintro ⟨e, he⟩
    refine ⟨withLeavesIso e _ _ ?_⟩
    intro v
    simp only [tagSize, he v, hN]

theorem isomorphic_graphOfSimple_iff {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    Isomorphic (graphOfSimple G) (graphOfSimple H) ↔ Nonempty (G ≃g H) := by
  classical
  constructor
  · rintro ⟨e, he⟩
    let E := (Fintype.equivFin V).trans (e.trans (Fintype.equivFin W).symm)
    refine ⟨{ toEquiv := E, map_rel_iff' := ?_ }⟩
    intro v w
    have hh := he (Fintype.equivFin V v) (Fintype.equivFin V w)
    change H.Adj ((Fintype.equivFin W).symm (e (Fintype.equivFin V v)))
      ((Fintype.equivFin W).symm (e (Fintype.equivFin V w))) ↔ G.Adj v w
    simpa [graphOfSimple, decide_eq_decide] using hh.symm
  · rintro ⟨e⟩
    let E := (Fintype.equivFin V).symm.trans (e.toEquiv.trans (Fintype.equivFin W))
    refine ⟨E, ?_⟩
    intro i j
    change decide (G.Adj ((Fintype.equivFin V).symm i) ((Fintype.equivFin V).symm j)) =
      decide (H.Adj ((Fintype.equivFin W).symm (Fintype.equivFin W
        (e ((Fintype.equivFin V).symm i))))
        ((Fintype.equivFin W).symm (Fintype.equivFin W (e ((Fintype.equivFin V).symm j)))))
    simp
    exact e.map_adj_iff.symm

end WLIdentification

end OAI
