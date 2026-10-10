import OAI.Computability.WLIdentification.BijectionGames

namespace OAI

namespace WLIdentification

namespace AffineBlocks

variable {C B : Type} [Fintype C] [DecidableEq C] [DecidableEq B]

structure OffsetFamily (D : AffineBlocks C B) (beta : B → Bit) (K : ℕ) where
  admissible : Finset B → (C → Bit) → Prop
  empty : ∃ x, admissible ∅ x
  legal : ∀ {U x}, admissible U x → ∀ b ∈ U, D.Legal beta b (D.restrict b x)
  restrict : ∀ {U V x}, V ⊆ U → admissible U x → admissible V x
  extend : ∀ {U x}, U.card < K → admissible U x → ∀ b,
    ∃ y, admissible (insert b U) y ∧ ∀ b' ∈ U, ∀ c ∈ D.coordinates b', y c = x c

/-- Purely local interfaces for the actual affine vertex translations. The
`piecewise` field is a bijection on vertices, not an asserted game strategy. -/
structure OwnedTranslations (D : AffineBlocks C B) (beta : B → Bit)
    {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) where
  owner : V → B
  images : (C → Bit) → V → W → Prop
  atomic : ∀ {x v v' w w'}, images x v w → images x v' w' →
    (v = v' ↔ w = w') ∧ (G.Adj v v' ↔ H.Adj w w')
  locality : ∀ {x y v w}, images x v w →
    (∀ c ∈ D.coordinates (owner v), y c = x c) → images y v w
  piecewise : ∀ f : B → C → Bit,
    (∀ b, D.Legal beta b (D.restrict b (f b))) →
    ∃ e : V ≃ W, ∀ v, images (f (owner v)) v (e v)

namespace OwnedTranslations

variable {D : AffineBlocks C B} {beta : B → Bit}
    {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

/-- Combining independently selected owner bijections gives one announced
vertex bijection before the next vertex is selected. -/
noncomputable def bijectionSystem (T : OwnedTranslations D beta G H)
    {K : ℕ} (F : OffsetFamily D beta K) :
    BijectionSystem (graphOfSimple G) (graphOfSimple H) K := by
  classical
  let ev := Fintype.equivFin V
  let ew := Fintype.equivFin W
  let support {m : ℕ} (v : Fin m → Fin (Fintype.card V)) : Finset B :=
    Finset.univ.image (fun i => T.owner (ev.symm (v i)))
  have hmem {m : ℕ} (v : Fin m → Fin (Fintype.card V)) (i : Fin m) :
      T.owner (ev.symm (v i)) ∈ support v := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  refine {
    relates := fun m v w => ∃ x, F.admissible (support v) x ∧
      ∀ i : Fin m, T.images x (ev.symm (v i)) (ew.symm (w i))
    empty := ?_
    restrict := ?_
    atomic := ?_
    extend := ?_ }
  · intro v w
    obtain ⟨x, hx⟩ := F.empty
    refine ⟨x, ?_, fun i => Fin.elim0 i⟩
    simpa only [support, Finset.univ_eq_empty, Finset.image_empty] using hx
  · intro m n v w hh f
    obtain ⟨x, hx, hi⟩ := hh
    refine ⟨x, F.restrict ?_ hx, fun i => hi (f i)⟩
    intro b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact hmem v (f i)
  · intro m v w hh
    obtain ⟨x, _, hi⟩ := hh
    constructor
    · intro i j
      exact (ev.symm.injective.eq_iff).symm.trans
        (((T.atomic (hi i) (hi j)).1).trans ew.symm.injective.eq_iff)
    · intro i j
      change decide (G.Adj (ev.symm (v i)) (ev.symm (v j))) =
        decide (H.Adj (ew.symm (w i)) (ew.symm (w j)))
      exact decide_eq_decide.mpr ((T.atomic (hi i) (hi j)).2)
  · intro m hm v w hh
    obtain ⟨x, hx, hi⟩ := hh
    have hcard : (support v).card < K := lt_of_le_of_lt
      (by simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m)))
        (f := fun i => T.owner (ev.symm (v i))))) hm
    have hext := F.extend hcard hx
    choose y hy hagree using hext
    have hlegal (b : B) : D.Legal beta b (D.restrict b (y b)) :=
      F.legal (hy b) b (Finset.mem_insert_self _ _)
    obtain ⟨e, he⟩ := T.piecewise y hlegal
    let E := ev.symm.trans (e.trans ew)
    refine ⟨E, ?_⟩
    intro z
    let b := T.owner (ev.symm z)
    refine ⟨y b, ?_, ?_⟩
    · apply F.restrict _ (hy b)
      intro b' hb'
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb'
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using Finset.mem_insert_self b (support v)
      · simpa only [Fin.snoc_castSucc] using Finset.mem_insert_of_mem (hmem v j)
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        change T.images (y b) (ev.symm z) (ew.symm (ew (e (ev.symm z))))
        simpa only [Equiv.symm_apply_apply] using he (ev.symm z)
      · simpa only [Fin.snoc_castSucc] using
          T.locality (hi j) (hagree b (T.owner (ev.symm (v j))) (hmem v j))

/-- Exact projection implies the literal joint-WL equivalence. -/
theorem equivalent (T : OwnedTranslations D beta G H) {K k : ℕ}
    (F : OffsetFamily D beta K) (hk : 2 ≤ k) (hkK : k < K) :
    Equivalent k (graphOfSimple G) (graphOfSimple H) :=
  (T.bijectionSystem F).equivalent hk hkK

end OwnedTranslations
end AffineBlocks

namespace AffineBlocks

variable {C B : Type} [Fintype C] [DecidableEq C]

abbrev BareVertex (D : AffineBlocks C B) := (C × Bit) ⊕ (Σ b, D.Local b)

def erase (D : AffineBlocks C B) {beta : B → Bit} : D.Vertex beta → D.BareVertex
  | .inl p => .inl p
  | .inr v => .inr ⟨v.1, v.2.val⟩

theorem erase_injective (D : AffineBlocks C B) (beta : B → Bit) :
    Function.Injective (D.erase (beta := beta)) := by
  intro v w h
  cases v with
  | inl p => cases w with
    | inl q => exact congrArg Sum.inl (Sum.inl.inj h)
    | inr w => cases h
  | inr v => cases w with
    | inl q => cases h
    | inr w =>
      obtain ⟨b, v⟩ := v
      obtain ⟨c, w⟩ := w
      have hbc : b = c := congrArg Sigma.fst (Sum.inr.inj h)
      subst c
      have hvw : v.val = w.val := by simpa only [erase, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
      exact congrArg (fun a => Sum.inr (Sigma.mk b a)) (Subtype.ext hvw)

def bareTranslation (D : AffineBlocks C B) (x : C → Bit) : D.BareVertex ≃ D.BareVertex :=
  Equiv.sumCongr
    (Equiv.prodCongrRight (fun c => Equiv.addRight (x c)))
    (Equiv.sigmaCongrRight (fun b => Equiv.addRight (D.restrict b x)))

def BaseImages (D : AffineBlocks C B) {beta : B → Bit}
    (x : C → Bit) (v : D.Vertex 0) (w : D.Vertex beta) : Prop :=
  D.erase w = D.bareTranslation x (D.erase v)

def BareAdj (D : AffineBlocks C B) : D.BareVertex → D.BareVertex → Prop
  | .inl p, .inr v => ∃ h : p.1 ∈ D.coordinates v.1, v.2 ⟨p.1, h⟩ = p.2
  | .inr v, .inl p => ∃ h : p.1 ∈ D.coordinates v.1, v.2 ⟨p.1, h⟩ = p.2
  | _, _ => False

theorem bareAdj_erase (D : AffineBlocks C B) {beta : B → Bit} (v w : D.Vertex beta) :
    D.BareAdj (D.erase v) (D.erase w) ↔ (D.baseGraph beta).Adj v w := by
  cases v <;> cases w <;> rfl

theorem bareAdj_translation (D : AffineBlocks C B) (x : C → Bit) (v w : D.BareVertex) :
    D.BareAdj (D.bareTranslation x v) (D.bareTranslation x w) ↔ D.BareAdj v w := by
  cases v with
  | inl p => cases w with
    | inl q => rfl
    | inr w =>
      change (∃ h : p.1 ∈ D.coordinates w.1,
        w.2 ⟨p.1, h⟩ + x p.1 = p.2 + x p.1) ↔ _
      simp only [add_left_inj]
      rfl
  | inr v => cases w with
    | inl p =>
      change (∃ h : p.1 ∈ D.coordinates v.1,
        v.2 ⟨p.1, h⟩ + x p.1 = p.2 + x p.1) ↔ _
      simp only [add_left_inj]
      rfl
    | inr w => rfl

theorem baseImages_atomic (D : AffineBlocks C B) {beta : B → Bit}
    {x : C → Bit} {v v' : D.Vertex 0} {w w' : D.Vertex beta}
    (h : D.BaseImages x v w) (h' : D.BaseImages x v' w') :
    (v = v' ↔ w = w') ∧ ((D.baseGraph 0).Adj v v' ↔ (D.baseGraph beta).Adj w w') := by
  constructor
  · rw [← (D.erase_injective 0).eq_iff, ← (D.bareTranslation x).injective.eq_iff,
      ← h, ← h', (D.erase_injective beta).eq_iff]
  · rw [← D.bareAdj_erase v v', ← D.bareAdj_erase w w', h, h', D.bareAdj_translation]

def vertexOwner (D : AffineBlocks C B) (owner : C → B) {beta : B → Bit} : D.Vertex beta → B
  | .inl p => owner p.1
  | .inr v => v.1

theorem baseImages_locality (D : AffineBlocks C B) (owner : C → B)
    (ho : ∀ c, c ∈ D.coordinates (owner c)) {beta : B → Bit}
    {x y : C → Bit} {v : D.Vertex 0} {w : D.Vertex beta}
    (h : D.BaseImages x v w)
    (ha : ∀ c ∈ D.coordinates (D.vertexOwner owner v), y c = x c) : D.BaseImages y v w := by
  unfold BaseImages at h ⊢
  rw [h]
  cases v with
  | inl p =>
    change Sum.inl (p.1, p.2 + x p.1) = Sum.inl (p.1, p.2 + y p.1)
    rw [ha p.1 (ho p.1)]
  | inr v =>
    change (Sum.inr ⟨v.1, v.2.val + D.restrict v.1 x⟩ : D.BareVertex) =
      Sum.inr ⟨v.1, v.2.val + D.restrict v.1 y⟩
    have he : D.restrict v.1 x = D.restrict v.1 y := by
      funext c
      exact (ha c.val c.property).symm
    rw [he]

def piecewiseTranslation (D : AffineBlocks C B) (owner : C → B) (beta : B → Bit)
    (f : B → C → Bit) (hf : ∀ b, D.Legal beta b (D.restrict b (f b))) :
    D.Vertex 0 ≃ D.Vertex beta :=
  Equiv.sumCongr
    (Equiv.prodCongrRight (fun c => Equiv.addRight (f (owner c) c)))
    (Equiv.sigmaCongrRight (fun b => D.legalTranslate b (D.restrict b (f b))
      (by intro h; simpa using hf b h)))

theorem piecewiseTranslation_images (D : AffineBlocks C B) (owner : C → B) (beta : B → Bit)
    (f : B → C → Bit) (hf : ∀ b, D.Legal beta b (D.restrict b (f b))) (v : D.Vertex 0) :
    D.BaseImages (f (D.vertexOwner owner v)) v (D.piecewiseTranslation owner beta f hf v) := by
  cases v <;> rfl

theorem baseImages_color (D : AffineBlocks C B) {beta : B → Bit}
    {x : C → Bit} {v : D.Vertex 0} {w : D.Vertex beta} (h : D.BaseImages x v w) :
    D.colorName w = D.colorName v := by
  let col : D.BareVertex → C ⊕ B := Sum.elim (fun p => .inl p.1) (fun v => .inr v.1)
  have he (u : D.BareVertex) : col (D.bareTranslation x u) = col u := by cases u <;> rfl
  have hv : col (D.erase v) = D.colorName v := by cases v <;> rfl
  have hw : col (D.erase w) = D.colorName w := by cases w <;> rfl
  rw [← hw, h, he, hv]

variable [DecidableEq B]

/-- The finite affine construction realizes the local interfaces with no
assumed graph isomorphism or winning strategy. -/
def baseTranslations (D : AffineBlocks C B) (owner : C → B)
    (ho : ∀ c, c ∈ D.coordinates (owner c)) (beta : B → Bit) :
    OwnedTranslations D beta (D.baseGraph 0) (D.baseGraph beta) where
  owner := D.vertexOwner owner
  images := D.BaseImages
  atomic := D.baseImages_atomic
  locality := D.baseImages_locality owner ho
  piecewise f hf := ⟨D.piecewiseTranslation owner beta f hf,
    D.piecewiseTranslation_images owner beta f hf⟩

end AffineBlocks

/-- Parent and private index give an injective description of leaf-coded vertices. -/
def leafParent {V : Type} {ell : V → ℕ} : LeafVertex ell → V
  | .inl v => v
  | .inr v => v.1

def leafIndex {V : Type} {ell : V → ℕ} : LeafVertex ell → Option ℕ
  | .inl _ => none
  | .inr v => some v.2.val

theorem leaf_eq_iff {V : Type} {ell : V → ℕ} (v w : LeafVertex ell) :
    v = w ↔ leafParent v = leafParent w ∧ leafIndex v = leafIndex w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hp, hi⟩
    cases v with
    | inl v => cases w with
      | inl w => exact congrArg Sum.inl hp
      | inr w => cases hi
    | inr v => cases w with
      | inl w => cases hi
      | inr w =>
        obtain ⟨v, i⟩ := v
        obtain ⟨w, j⟩ := w
        change v = w at hp
        subst w
        have hij : i = j := Fin.ext (Option.some.inj hi)
        subst j
        rfl

theorem withLeaves_adj_iff {V : Type} (G : SimpleGraph V) (ell : V → ℕ)
    (v w : LeafVertex ell) : (withLeaves G ell).Adj v w ↔
      if leafIndex v = none then
        if leafIndex w = none then G.Adj (leafParent v) (leafParent w)
        else leafParent v = leafParent w
      else if leafIndex w = none then leafParent v = leafParent w else False := by
  cases v <;> cases w <;> simp only [leafIndex, leafParent, withLeaves,
    ite_true, Option.some_ne_none, ite_false]

namespace AffineBlocks.OwnedTranslations

variable {C B V W : Type} [Fintype C] [DecidableEq C] [DecidableEq B]
    {D : AffineBlocks C B} {beta : B → Bit} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Private leaves extend local translations exactly, retaining each private
index; this is used before the owner pieces are combined into a game bijection. -/
def withLeaves (T : OwnedTranslations D beta G H) (ell : V → ℕ) (ell' : W → ℕ)
    (hl : ∀ {x v w}, T.images x v w → ell v = ell' w) :
    OwnedTranslations D beta (WLIdentification.withLeaves G ell)
      (WLIdentification.withLeaves H ell') where
  owner v := T.owner (leafParent v)
  images x v w := T.images x (leafParent v) (leafParent w) ∧ leafIndex v = leafIndex w
  atomic := by
    intro x v v' w w' h h'
    obtain ⟨he, ha⟩ := T.atomic h.1 h'.1
    constructor
    · rw [leaf_eq_iff, leaf_eq_iff, he, h.2, h'.2]
    · rw [withLeaves_adj_iff, withLeaves_adj_iff, ← h.2, ← h'.2]
      split <;> split
      · exact ha
      · exact he
      · exact he
      · rfl
  locality := by
    intro x y v w h hh
    exact ⟨T.locality h.1 hh, h.2⟩
  piecewise := by
    intro f hf
    obtain ⟨e, he⟩ := T.piecewise f hf
    let E : LeafVertex ell ≃ LeafVertex ell' :=
      Equiv.sumCongr e (Equiv.sigmaCongr e (fun v => finCongr (hl (he v))))
    refine ⟨E, ?_⟩
    intro v
    cases v with
    | inl v => exact ⟨he v, rfl⟩
    | inr v => exact ⟨he v.1, rfl⟩

end AffineBlocks.OwnedTranslations

namespace AffineBlocks
variable {C B : Type} [Fintype C] [DecidableEq C] [Fintype B] [DecidableEq B]

/-- Complete interface from exact-projection coordinate families to the actual
uncolored graphs, with every private leaf and its owner included. -/
noncomputable def taggedTranslations (D : AffineBlocks C B) (owner : C → B)
    (ho : ∀ c, c ∈ D.coordinates (owner c)) (beta : B → Bit) :
    OwnedTranslations D beta
      (withLeaves (D.baseGraph 0) (tagSize D.colorNat))
      (withLeaves (D.baseGraph beta) (tagSize D.colorNat)) :=
  (D.baseTranslations owner ho beta).withLeaves _ _ (by
    intro x v w h
    have hc : D.colorNat w = D.colorNat v :=
      (D.colorNat_eq_iff w v).mpr (D.baseImages_color h)
    dsimp only [tagSize]
    rw [hc, D.vertex_card 0 beta])

theorem graph_equivalent_of_offsetFamily (D : AffineBlocks C B) (owner : C → B)
    (ho : ∀ c, c ∈ D.coordinates (owner c)) (beta : B → Bit) {K k : ℕ}
    (F : D.OffsetFamily beta K) (hk : 2 ≤ k) (hkK : k < K) :
    Equivalent k (D.graph 0) (D.graph beta) :=
  (D.taggedTranslations owner ho beta).equivalent F hk hkK

end AffineBlocks

end WLIdentification

end OAI
