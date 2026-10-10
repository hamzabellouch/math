import OAI.Computability.WLIdentification.PrivateLeaves

namespace OAI

namespace WLIdentification

abbrev Bit := ZMod 2

/- Fixed-depth natural codes. Unlike arbitrary finite enumerations these are
literal arithmetic presentations, so tag sizes can be generated uniformly. -/
namespace NaturalCode
variable {A B : Type}

def fin (n : ℕ) : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
def bool : Bool ↪ ℕ := ⟨fun b => if b then 1 else 0, by decide⟩
def unit : Unit ↪ ℕ := ⟨fun _ => 0, fun _ _ _ => rfl⟩
def prod (a : A ↪ ℕ) (b : B ↪ ℕ) : A × B ↪ ℕ :=
  (a.prodMap b).trans Nat.pairEquiv.toEmbedding

def sum (a : A ↪ ℕ) (b : B ↪ ℕ) : A ⊕ B ↪ ℕ where
  toFun
    | .inl x => 2 * a x
    | .inr y => 2 * b y + 1
  inj' := by
    intro x y h
    cases x <;> cases y
    · exact congrArg Sum.inl (a.injective (by dsimp at h; omega))
    · dsimp at h; omega
    · dsimp at h; omega
    · exact congrArg Sum.inr (b.injective (by dsimp at h; omega))

def option (a : A ↪ ℕ) : Option A ↪ ℕ where
  toFun
    | none => 0
    | some x => a x + 1
  inj' := by
    intro x y h
    cases x <;> cases y
    · rfl
    · dsimp at h; omega
    · dsimp at h; omega
    · exact congrArg some (a.injective (by dsimp at h; omega))

def subtype (a : A ↪ ℕ) (p : A → Prop) : {x // p x} ↪ ℕ :=
  (Function.Embedding.subtype _).trans a

def sigma {B : A → Type} (a : A ↪ ℕ) (b : ∀ x, B x ↪ ℕ) : (Σ x, B x) ↪ ℕ where
  toFun x := Nat.pair (a x.1) (b x.1 x.2)
  inj' := by
    rintro ⟨x,u⟩ ⟨y,v⟩ h
    obtain ⟨hx,hv⟩ := Nat.pair_eq_pair.mp h
    have he := a.injective hx
    dsimp only at he hv
    subst y
    have hu := (b x).injective hv
    subst v
    rfl

noncomputable def fixed (A : Type) [Fintype A] : A ↪ ℕ :=
  (Fintype.equivFin A).toEmbedding.trans (fin _)

end NaturalCode

structure AffineBlocks (C B : Type) [Fintype C] [DecidableEq C] where
  colorIndex : (C ⊕ B) ↪ ℕ
  coordinates : B → Finset C
  form : (b : B) → ((c : coordinates b) → Bit) →ₗ[Bit] Bit
  constrained : B → Bool
  nonzero : ∀ b, constrained b = true → form b ≠ 0

namespace AffineBlocks

variable {C B : Type} [Fintype C] [DecidableEq C]

abbrev Local (D : AffineBlocks C B) (b : B) := (c : D.coordinates b) → Bit

def Legal (D : AffineBlocks C B) (beta : B → Bit) (b : B) (v : D.Local b) : Prop :=
  D.constrained b = true → D.form b v = beta b

noncomputable instance legalDecidable (D : AffineBlocks C B) (beta : B → Bit) (b : B) :
    DecidablePred (D.Legal beta b) := Classical.decPred _

def restrict (D : AffineBlocks C B) (b : B) (x : C → Bit) : D.Local b := fun c => x c.val

def Solves (D : AffineBlocks C B) (beta : B → Bit) (x : C → Bit) : Prop :=
  ∀ b, D.Legal beta b (D.restrict b x)

theorem local_nonempty (D : AffineBlocks C B) (beta : B → Bit) (b : B) :
    ∃ v, D.Legal beta b v := by
  by_cases hc : D.constrained b = true
  · obtain ⟨v, hv⟩ := LinearMap.surjective_of_ne_zero (D.nonzero b hc) (beta b)
    exact ⟨v, fun _ => hv⟩
  · exact ⟨0, fun h => False.elim (hc h)⟩

theorem legal_zero (D : AffineBlocks C B) (b : B) : D.Legal 0 b 0 := by
  intro _
  exact map_zero _

/-- Only local nonemptiness is used here; no simultaneous solution is presumed. -/
def legalTranslate (D : AffineBlocks C B) {beta gamma : B → Bit} (b : B)
    (offset : D.Local b) (ho : ∀ _ : D.constrained b = true,
      D.form b offset = gamma b - beta b) :
    {v // D.Legal beta b v} ≃ {v // D.Legal gamma b v} where
  toFun v := ⟨v.val + offset, by
    intro h
    rw [map_add, v.property h, ho h]
    abel⟩
  invFun v := ⟨v.val - offset, by
    intro h
    rw [map_sub, v.property h, ho h]
    abel⟩
  left_inv v := by ext c; simp
  right_inv v := by ext c; simp

theorem legal_card (D : AffineBlocks C B) (beta gamma : B → Bit) (b : B) :
    Fintype.card {v // D.Legal beta b v} = Fintype.card {v // D.Legal gamma b v} := by
  classical
  obtain ⟨o, ho⟩ := D.local_nonempty (gamma - beta) b
  exact Fintype.card_congr (D.legalTranslate b o ho)

abbrev Vertex (D : AffineBlocks C B) (beta : B → Bit) :=
  (C × Bit) ⊕ (Σ b, {v // D.Legal beta b v})

def colorName (D : AffineBlocks C B) {beta : B → Bit} : D.Vertex beta → C ⊕ B
  | .inl p => .inl p.1
  | .inr v => .inr v.1

def baseGraph (D : AffineBlocks C B) (beta : B → Bit) : SimpleGraph (D.Vertex beta) where
  Adj u v := match u, v with
    | .inl p, .inr w => ∃ h : p.1 ∈ D.coordinates w.1, w.2.val ⟨p.1, h⟩ = p.2
    | .inr w, .inl p => ∃ h : p.1 ∈ D.coordinates w.1, w.2.val ⟨p.1, h⟩ = p.2
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> exact id⟩
  loopless := ⟨by intro u; cases u <;> exact not_false⟩

noncomputable instance baseGraph_decidable (D : AffineBlocks C B) (beta : B → Bit) :
    DecidableRel (D.baseGraph beta).Adj := Classical.decRel _

/-- Translation uses the same named coordinate offset in every incident block. -/
def translationIso (D : AffineBlocks C B) (beta : B → Bit)
    (offset : C → Bit) (ho : D.Solves beta offset) : D.baseGraph 0 ≃g D.baseGraph beta where
  toEquiv := Equiv.sumCongr
    (Equiv.prodCongrRight (fun c => Equiv.addRight (offset c)))
    (Equiv.sigmaCongrRight (fun b => D.legalTranslate b (D.restrict b offset)
      (by intro h; simpa using ho b h)))
  map_rel_iff' := by
    intro x y
    cases x with
    | inl p =>
      cases y with
      | inl q => rfl
      | inr v =>
        change (∃ h : p.1 ∈ D.coordinates v.1,
          v.2.val ⟨p.1, h⟩ + offset p.1 = p.2 + offset p.1) ↔ _
        simp only [add_left_inj]
        rfl
    | inr v =>
      cases y with
      | inl p =>
        change (∃ h : p.1 ∈ D.coordinates v.1,
          v.2.val ⟨p.1, h⟩ + offset p.1 = p.2 + offset p.1) ↔ _
        simp only [add_left_inj]
        rfl
      | inr w => rfl

@[simp]
theorem translationIso_color (D : AffineBlocks C B) (beta : B → Bit)
    (offset : C → Bit) (ho : D.Solves beta offset) (v : D.Vertex 0) :
    D.colorName (D.translationIso beta offset ho v) = D.colorName v := by
  cases v <;> rfl

theorem exists_bit_of_color (D : AffineBlocks C B) {beta : B → Bit}
    (v : D.Vertex beta) (c : C) (h : D.colorName v = .inl c) :
    ∃ a, v = .inl (c, a) := by
  cases v with
  | inl p =>
    have hp : p.1 = c := Sum.inl.inj h
    exact ⟨p.2, by cases p; simp_all⟩
  | inr w => simp [colorName] at h

theorem exists_valuation_of_color (D : AffineBlocks C B) {beta : B → Bit}
    (v : D.Vertex beta) (b : B) (h : D.colorName v = .inr b) :
    ∃ w : {w // D.Legal beta b w}, v = .inr ⟨b, w⟩ := by
  cases v with
  | inl p => simp [colorName] at h
  | inr w =>
    obtain ⟨b', w⟩ := w
    have hb : b' = b := Sum.inr.inj h
    subst b'
    exact ⟨w, rfl⟩

/-- All-zero valuations extract one global offset from a color-preserving
isomorphism. No agreement between independently chosen block maps is assumed. -/
theorem coloredIso_solution (D : AffineBlocks C B) (beta : B → Bit)
    (e : D.baseGraph 0 ≃g D.baseGraph beta)
    (he : ∀ v, D.colorName (e v) = D.colorName v) :
    ∃ offset, D.Solves beta offset := by
  classical
  have hc (c : C) : ∃ a, e (.inl (c, 0)) = .inl (c, a) :=
    D.exists_bit_of_color _ c (he _)
  choose offset hoff using hc
  refine ⟨offset, ?_⟩
  intro b
  let z : {v // D.Legal 0 b v} := ⟨0, D.legal_zero b⟩
  obtain ⟨w, hw⟩ := D.exists_valuation_of_color (e (.inr ⟨b, z⟩)) b (he _)
  have hval : w.val = D.restrict b offset := by
    funext c
    have hs : (D.baseGraph 0).Adj (.inr ⟨b, z⟩) (.inl (c.val, 0)) := ⟨c.property, rfl⟩
    have ht := e.map_adj_iff.mpr hs
    rw [hw, hoff c.val] at ht
    obtain ⟨hc, hvalue⟩ := ht
    exact hvalue
  rw [← hval]
  exact w.property

theorem coloredIso_iff (D : AffineBlocks C B) (beta : B → Bit) :
    (∃ e : D.baseGraph 0 ≃g D.baseGraph beta,
      ∀ v, D.colorName (e v) = D.colorName v) ↔ ∃ offset, D.Solves beta offset := by
  constructor
  · rintro ⟨e, he⟩
    exact D.coloredIso_solution beta e he
  · rintro ⟨offset, ho⟩
    exact ⟨D.translationIso beta offset ho, D.translationIso_color beta offset ho⟩

variable [Fintype B]

noncomputable def colorNat (D : AffineBlocks C B) {beta : B → Bit} (v : D.Vertex beta) : ℕ :=
  D.colorIndex (D.colorName v) + 1

omit [Fintype B] in
theorem colorNat_pos (D : AffineBlocks C B) {beta : B → Bit} (v : D.Vertex beta) :
    0 < D.colorNat v := Nat.zero_lt_succ _

omit [Fintype B] in
theorem colorNat_eq_iff (D : AffineBlocks C B) {beta gamma : B → Bit}
    (v : D.Vertex beta) (w : D.Vertex gamma) :
    D.colorNat v = D.colorNat w ↔ D.colorName v = D.colorName w := by
  simp only [colorNat, Nat.add_right_cancel_iff]
  constructor
  · intro h
    exact D.colorIndex.injective h
  · exact congrArg D.colorIndex

theorem vertex_card (D : AffineBlocks C B) (beta gamma : B → Bit) :
    Fintype.card (D.Vertex beta) = Fintype.card (D.Vertex gamma) := by
  simp only [Vertex, Fintype.card_sum, Fintype.card_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact D.legal_card beta gamma b

noncomputable def graph (D : AffineBlocks C B) (beta : B → Bit) : Graph :=
  taggedGraph (D.baseGraph beta) D.colorNat

theorem graph_isomorphic_iff (D : AffineBlocks C B) (beta : B → Bit) :
    Isomorphic (D.graph 0) (D.graph beta) ↔ ∃ offset, D.Solves beta offset := by
  unfold graph taggedGraph
  rw [isomorphic_graphOfSimple_iff, taggedIso_iff _ _ _ _ D.colorNat_pos D.colorNat_pos
    (D.vertex_card 0 beta)]
  rw [← D.coloredIso_iff beta]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun v => (D.colorNat_eq_iff v (e v)).mp (he v) |>.symm⟩
  · rintro ⟨e, he⟩
    exact ⟨e, fun v => (D.colorNat_eq_iff v (e v)).mpr (he v).symm⟩

omit [Fintype B]

/-- A complete bounded incidence piece consists of its valuation class and both
vertices of every bit pair used by this block. -/
abbrev Piece (D : AffineBlocks C B) (beta : B → Bit) (b : B) :=
  (D.coordinates b × Bit) ⊕ {v // D.Legal beta b v}

def pieceEmbed (D : AffineBlocks C B) {beta : B → Bit} (b : B) :
    D.Piece beta b ↪ D.Vertex beta where
  toFun x := match x with
    | .inl p => .inl (p.1.val, p.2)
    | .inr v => .inr ⟨b, v⟩
  inj' := by
    intro x y h
    cases x <;> cases y
    · simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      apply congrArg Sum.inl
      exact Prod.ext (Subtype.ext h1) h2
    · cases h
    · cases h
    · simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      exact congrArg Sum.inr h

def pieceGraph (D : AffineBlocks C B) (beta : B → Bit) (b : B) :
    SimpleGraph (D.Piece beta b) := (D.baseGraph beta).comap (D.pieceEmbed b)

theorem bit_cases (a : Bit) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · exact Or.inl ((ZMod.val_injective 2) h)
  · exact Or.inr ((ZMod.val_injective 2) h)

theorem bit_injective_translation (f : Bit → Bit) (hf : Function.Injective f) (a : Bit) :
    f a = a + f 0 := by
  have h01 : f 0 ≠ f 1 := hf.ne (by decide)
  rcases bit_cases a with rfl | rfl
  · simp
  · rcases bit_cases (f 0) with h0 | h0 <;>
      rcases bit_cases (f 1) with h1 | h1 <;> simp_all
    decide

theorem piece_bit_of_color (D : AffineBlocks C B) {beta : B → Bit} (b : B)
    (v : D.Piece beta b) (c : D.coordinates b)
    (h : D.colorName (D.pieceEmbed b v) = .inl c.val) :
    ∃ a, v = .inl (c, a) := by
  cases v with
  | inl p =>
    have hp : p.1.val = c.val := Sum.inl.inj h
    have hp' : p.1 = c := Subtype.ext hp
    exact ⟨p.2, by cases p; simp_all⟩
  | inr w => simp [pieceEmbed, colorName] at h

theorem piece_valuation_of_color (D : AffineBlocks C B) {beta : B → Bit} (b : B)
    (v : D.Piece beta b) (h : D.colorName (D.pieceEmbed b v) = .inr b) :
    ∃ w, v = .inr w := by
  cases v with
  | inl p => simp [pieceEmbed, colorName] at h
  | inr w => exact ⟨w, rfl⟩

/-- One entire incidence piece determines a shifted equation in any fixed
labeling of its bit pairs. Coordinate flips in different pieces need not agree. -/
theorem local_reconstruction (D : AffineBlocks C B) (H : SimpleGraph (D.Vertex 0)) (b : B)
    (e : D.pieceGraph 0 b ≃g H.comap (D.pieceEmbed b))
    (he : ∀ v, D.colorName (D.pieceEmbed b (e v)) = D.colorName (D.pieceEmbed b v)) :
    ∃ offset : D.Local b, ∃ E : {v // D.Legal 0 b v} ≃ {v // D.Legal 0 b v},
      ∀ (v : {v // D.Legal 0 b v}) (c : D.coordinates b) (a : Bit),
        H.Adj (.inl (c.val, a)) (.inr ⟨b, E v⟩) ↔ v.val c + offset c = a := by
  classical
  have hbit (c : D.coordinates b) (a : Bit) : ∃ w, e (.inl (c, a)) = .inl (c, w) :=
    D.piece_bit_of_color b _ c (he _)
  choose f hf using hbit
  have hfinj (c : D.coordinates b) : Function.Injective (f c) := by
    intro a a' h
    have hh : e (.inl (c, a)) = e (.inl (c, a')) := by rw [hf, hf, h]
    have hh' := e.injective hh
    exact (Prod.mk.inj (Sum.inl.inj hh')).2
  have hftrans (c : D.coordinates b) (a : Bit) : f c a = a + f c 0 :=
    bit_injective_translation (f c) (hfinj c) a
  have hval (v : {v // D.Legal 0 b v}) : ∃ w, e (.inr v) = .inr w :=
    D.piece_valuation_of_color b _ (he _)
  choose fv hfv using hval
  have hfvinj : Function.Injective fv := by
    intro v w h
    have hh : e (.inr v) = e (.inr w) := by rw [hfv, hfv, h]
    exact Sum.inr.inj (e.injective hh)
  let E := Equiv.ofBijective fv ((Fintype.bijective_iff_injective_and_card fv).mpr ⟨hfvinj, rfl⟩)
  refine ⟨fun c => f c 0, E, ?_⟩
  intro v c a
  have hh := e.map_adj_iff (v := Sum.inl (c, a - f c 0)) (w := Sum.inr v)
  rw [hf, hfv, hftrans, sub_add_cancel] at hh
  change H.Adj (.inl (c.val, a)) (.inr ⟨b, fv v⟩) ↔
    (∃ h : c.val ∈ D.coordinates b, v.val ⟨c.val, h⟩ = a - f c 0) at hh
  simp only [Subtype.coe_eta, exists_prop_of_true c.property] at hh
  exact hh.trans (eq_sub_iff_add_eq)

/-- Adjacencies are allowed only between a valuation class and a named bit
coordinate used by that block. This records no right-hand-side information. -/
def Allowed (D : AffineBlocks C B) {beta : B → Bit} (x y : D.Vertex beta) : Prop :=
  match x, y with
  | .inl c, .inr v => c.1 ∈ D.coordinates v.1
  | .inr v, .inl c => c.1 ∈ D.coordinates v.1
  | _, _ => False

theorem base_adj_allowed (D : AffineBlocks C B) {beta : B → Bit} {x y : D.Vertex beta}
    (h : (D.baseGraph beta).Adj x y) : D.Allowed x y := by
  cases x <;> cases y
  · exact h
  · exact h.choose
  · exact h.choose
  · exact h

/-- Combining the independently reconstructed pieces uses a single labeling of
all shared bit pairs, but permits one independent right-hand side per block. -/
theorem base_reconstruction (D : AffineBlocks C B) (H : SimpleGraph (D.Vertex 0))
    (hallowed : ∀ x y, H.Adj x y → D.Allowed x y)
    (hlocal : ∀ b, ∃ e : D.pieceGraph 0 b ≃g H.comap (D.pieceEmbed b),
      ∀ v, D.colorName (D.pieceEmbed b (e v)) = D.colorName (D.pieceEmbed b v)) :
    ∃ beta, ∃ e : D.baseGraph beta ≃g H, ∀ v, D.colorName (e v) = D.colorName v := by
  classical
  have hr (b : B) :
      ∃ offset : D.Local b, ∃ E : {v // D.Legal 0 b v} ≃ {v // D.Legal 0 b v},
        ∀ (v : {v // D.Legal 0 b v}) (c : D.coordinates b) (a : Bit),
          H.Adj (.inl (c.val, a)) (.inr ⟨b, E v⟩) ↔ v.val c + offset c = a := by
    obtain ⟨e, he⟩ := hlocal b
    exact D.local_reconstruction H b e he
  choose offset E hE using hr
  let beta : B → Bit := fun b => D.form b (offset b)
  let T (b : B) : {v // D.Legal 0 b v} ≃ {v // D.Legal beta b v} :=
    D.legalTranslate b (offset b) (fun _ => by simp [beta])
  let eV (b : B) := (T b).symm.trans (E b)
  let e : D.Vertex beta ≃ D.Vertex 0 :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaCongrRight eV)
  have hbits (b : B) (v : {v // D.Legal beta b v}) (c : D.coordinates b) (a : Bit) :
      H.Adj (.inl (c.val, a)) (.inr ⟨b, eV b v⟩) ↔ v.val c = a := by
    have hh := hE b ((T b).symm v) c a
    change H.Adj (.inl (c.val, a)) (.inr ⟨b, eV b v⟩) ↔
      v.val c - offset b c + offset b c = a at hh
    simpa only [sub_add_cancel] using hh
  refine ⟨beta, { toEquiv := e, map_rel_iff' := ?_ }, ?_⟩
  · intro x y
    cases x with
    | inl p =>
      cases y with
      | inl q =>
        change H.Adj (.inl p) (.inl q) ↔ False
        exact ⟨hallowed _ _, False.elim⟩
      | inr v =>
        change H.Adj (.inl p) (.inr ⟨v.1, eV v.1 v.2⟩) ↔
          (∃ h : p.1 ∈ D.coordinates v.1, v.2.val ⟨p.1, h⟩ = p.2)
        by_cases hc : p.1 ∈ D.coordinates v.1
        · simpa only [exists_prop_of_true hc] using hbits v.1 v.2 ⟨p.1, hc⟩ p.2
        · exact ⟨fun h => False.elim (hc (hallowed _ _ h)), fun h => False.elim (hc h.choose)⟩
    | inr v =>
      cases y with
      | inl p =>
        change H.Adj (.inr ⟨v.1, eV v.1 v.2⟩) (.inl p) ↔
          (∃ h : p.1 ∈ D.coordinates v.1, v.2.val ⟨p.1, h⟩ = p.2)
        rw [H.adj_comm]
        by_cases hc : p.1 ∈ D.coordinates v.1
        · simpa only [exists_prop_of_true hc] using hbits v.1 v.2 ⟨p.1, hc⟩ p.2
        · exact ⟨fun h => False.elim (hc (hallowed _ _ h)), fun h => False.elim (hc h.choose)⟩
      | inr w =>
        change H.Adj (.inr ⟨v.1, eV v.1 v.2⟩) (.inr ⟨w.1, eV w.1 w.2⟩) ↔ False
        exact ⟨hallowed _ _, False.elim⟩
  · intro v
    cases v <;> rfl

end AffineBlocks

end WLIdentification

end OAI
