import OAI.Computability.WeisfeilerLeman.Wrapping

namespace OAI

universe uB uV uLabel uP uE uΛ

namespace WLTime.Compression
namespace BlockDrawing
variable {r : ℕ} {B : Type uB} {V : Type uV} {Label : Type uLabel} [DecidableEq Label] (D : BlockDrawing r B V)

theorem address_exists (hr : 2 ≤ r) (U : Finset B) (label : V → Label)
    (align : ∀ b ∈ U, label (D.low b false) = label (D.low b true) ∧
      label (D.high b false) = label (D.high b true))
    (h : D.Wraps U) (hc : U.card = r + 1) :
    ∃ a : Fin (r + 1) → Label, ∀ b ∈ U, ∀ s,
      label (D.low b s) = a (D.row b) ∧
      label (D.high b s) = a (finRotate (r + 1) (D.row b)) := by
  classical
  have hex := D.wraps_unique_row hr U h hc
  choose f hf huniq using hex
  let lo := fun i => label (D.low (f i) false)
  let hi := fun i => label (D.high (f i) false)
  have hlabels : ∀ b ∈ U, ∀ s, label (D.low b s) = lo (D.row b) ∧
      label (D.high b s) = hi (D.row b) := by
    intro b hb s
    have hbf := huniq (D.row b) b ⟨hb, rfl⟩
    constructor
    · exact (D.side_label_low label (align b hb).1 s).trans (congrArg (fun b => label (D.low b false)) hbf)
    · exact (D.side_label_high label (align b hb).2 s).trans (congrArg (fun b => label (D.high b false)) hbf)
  have hjoin := D.wrapping_labels_join hr U label lo hi hlabels h
  exact ⟨lo, fun b hb s => ⟨(hlabels b hb s).1, (hlabels b hb s).2.trans (hjoin (D.row b))⟩⟩

omit [DecidableEq Label] in

theorem addresses_agree [DecidableEq B] (hr : 2 ≤ r) (U A C : Finset B)
    (hA : A ⊆ U) (hC : C ⊆ U) (hcard : U.card ≤ r + 2)
    (hwrap : D.Wraps A) (hsizeA : A.card = r + 1) (hsizeC : C.card = r + 1)
    (label : V → Label) (a c : Fin (r + 1) → Label)
    (ha : ∀ b ∈ A, ∀ s, label (D.low b s) = a (D.row b) ∧
      label (D.high b s) = a (finRotate (r + 1) (D.row b)))
    (hc : ∀ b ∈ C, ∀ s, label (D.low b s) = c (D.row b) ∧
      label (D.high b s) = c (finRotate (r + 1) (D.row b))) : a = c := by
  apply recovered_addresses_agree (finRotate (r + 1)) (rotate_ne_self (by omega)) D.row
    (fun b => label (D.low b false)) (fun b => label (D.high b false))
    U A C hA hC (r + 1) hsizeC (by omega)
  · intro i
    obtain ⟨b, hb, _⟩ := D.wraps_unique_row hr A hwrap hsizeA i
    exact ⟨b, hb⟩
  · exact fun b hb => ⟨(ha b hb false).1.symm, (ha b hb false).2.symm⟩
  · exact fun b hb => ⟨(hc b hb false).1.symm, (hc b hb false).2.symm⟩

end BlockDrawing
end WLTime.Compression

namespace WLTime.Compression

variable {P : Type uP} {E : Type uE}

abbrev TypeNode (K : ℕ) (P : Type uP) (E : Type uE) := P ⊕ (E × Fin (4 * K))
abbrev TypeLink (K : ℕ) (E : Type uE) := E × Fin (4 * K + 1)

def linkLeft (K : ℕ) (src : E → P) (l : TypeLink K E) : TypeNode K P E :=
  if h : l.2.val = 0 then Sum.inl (src l.1)
  else Sum.inr (l.1, ⟨l.2.val - 1, by have := l.2.isLt; omega⟩)

def linkRight (K : ℕ) (dst : E → P) (l : TypeLink K E) : TypeNode K P E :=
  if h : l.2.val = 4 * K then Sum.inl (dst l.1)
  else Sum.inr (l.1, ⟨l.2.val, by have := l.2.isLt; omega⟩)

def typeDepth (K : ℕ) : TypeNode K P E → ℕ
  | .inl _ => 0
  | .inr (_, j) => min (j.val + 1) (4 * K - j.val)

def realRoot (K : ℕ) (src dst : E → P) : TypeNode K P E → P
  | .inl p => p
  | .inr (e, j) => if j.val < 2 * K then src e else dst e

def linkDepth (K : ℕ) (src dst : E → P) (l : TypeLink K E) : ℕ :=
  min (typeDepth K (linkLeft K src l)) (typeDepth K (linkRight K dst l))

theorem link_depth_near (K : ℕ) (src dst : E → P) (l : TypeLink K E) :
    typeDepth K (linkLeft K src l) ≤ typeDepth K (linkRight K dst l) + 1 ∧
    typeDepth K (linkRight K dst l) ≤ typeDepth K (linkLeft K src l) + 1 := by
  have hj := l.2.isLt
  dsimp only [linkLeft, linkRight]
  split_ifs <;> simp only [typeDepth] <;> omega

theorem link_midpoint_depth (K : ℕ) (src dst : E → P) (hK : 0 < K)
    (l : TypeLink K E) (hl : l.2.val = 2 * K) :
    typeDepth K (linkLeft K src l) = 2 * K ∧
    typeDepth K (linkRight K dst l) = 2 * K := by
  have h0 : l.2.val ≠ 0 := by omega
  have h4 : l.2.val ≠ 4 * K := by omega
  simp only [linkLeft, linkRight, dite_eq_right h0, dite_eq_right h4, typeDepth]
  omega

theorem link_root_preserved (K : ℕ) (src dst : E → P) (hK : 0 < K)
    (l : TypeLink K E) (hl : l.2.val ≠ 2 * K) :
    realRoot K src dst (linkLeft K src l) = realRoot K src dst (linkRight K dst l) := by
  have hj := l.2.isLt
  dsimp only [linkLeft, linkRight]
  split_ifs <;> simp only [realRoot]
  all_goals (try split_ifs) <;> first | rfl | omega

theorem exists_missing_depth [DecidableEq E] (K : ℕ) (src dst : E → P) (hK : 0 < K)
    (S : Finset (TypeLink K E)) (hS : S.card ≤ K) :
    ∃ h, h < 2 * K ∧ ∀ l ∈ S, linkDepth K src dst l ≠ h := by
  classical
  by_contra! h
  have hsub : Finset.range (2 * K) ⊆ S.image (linkDepth K src dst) := by
    intro a ha
    obtain ⟨l, hl, heq⟩ := h a (Finset.mem_range.mp ha)
    exact Finset.mem_image.mpr ⟨l, hl, heq⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  simp only [Finset.card_range] at hc
  omega

def typeSupportGraph (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E)) :
    SimpleGraph (TypeNode K P E) where
  Adj x y := x ≠ y ∧ ∃ l ∈ S,
    (x = linkLeft K src l ∧ y = linkRight K dst l) ∨
    (x = linkRight K dst l ∧ y = linkLeft K src l)
  symm := ⟨by
    rintro x y ⟨hxy, l, hl, h | h⟩
    · exact ⟨hxy.symm, l, hl, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨hxy.symm, l, hl, Or.inl ⟨h.2, h.1⟩⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

private theorem equal_cut_of_near {a b h : ℕ} (hab : a ≤ b + 1) (hba : b ≤ a + 1)
    (hh : min a b ≠ h) : (a ≤ h ↔ b ≤ h) := by omega

theorem support_cut_preserved (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E))
    (h : ℕ) (hh : ∀ l ∈ S, linkDepth K src dst l ≠ h)
    {x y : TypeNode K P E} (hxy : (typeSupportGraph K src dst S).Adj x y) :
    (typeDepth K x ≤ h ↔ typeDepth K y ≤ h) := by
  obtain ⟨_, l, hl, he | he⟩ := hxy
  · obtain ⟨rfl, rfl⟩ := he
    exact equal_cut_of_near (link_depth_near K src dst l).1
      (link_depth_near K src dst l).2 (hh l hl)
  · obtain ⟨rfl, rfl⟩ := he
    exact (equal_cut_of_near (link_depth_near K src dst l).1
      (link_depth_near K src dst l).2 (hh l hl)).symm

theorem support_walk_cut (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E))
    (h : ℕ) (hh : ∀ l ∈ S, linkDepth K src dst l ≠ h)
    {x y : TypeNode K P E} (w : (typeSupportGraph K src dst S).Walk x y) :
    (typeDepth K x ≤ h ↔ typeDepth K y ≤ h) := by
  induction w with
  | nil => rfl
  | cons hxy w ih => exact (support_cut_preserved K src dst S h hh hxy).trans ih

theorem reachable_real_depth [DecidableEq E] (K : ℕ) (src dst : E → P) (hK : 0 < K)
    (S : Finset (TypeLink K E)) (hS : S.card ≤ K) (p : P)
    {t : TypeNode K P E} (ht : (typeSupportGraph K src dst S).Reachable (.inl p) t) :
    typeDepth K t < 2 * K := by
  obtain ⟨h, hh, hmissing⟩ := exists_missing_depth K src dst hK S hS
  obtain ⟨w⟩ := ht
  have hd := (support_walk_cut K src dst S h hmissing w).mp (Nat.zero_le h)
  exact lt_of_le_of_lt hd hh

end WLTime.Compression

namespace WLTime.Compression

variable {P : Type uP} {E : Type uE}

theorem support_edge_root_of_real [DecidableEq E] (K : ℕ) (src dst : E → P)
    (hK : 0 < K) (S : Finset (TypeLink K E)) (hS : S.card ≤ K) (p : P)
    {x y : TypeNode K P E} (hx : (typeSupportGraph K src dst S).Reachable (.inl p) x)
    (hxy : (typeSupportGraph K src dst S).Adj x y) :
    realRoot K src dst x = realRoot K src dst y := by
  obtain ⟨_, l, _, he | he⟩ := hxy
  · obtain ⟨rfl, rfl⟩ := he
    apply link_root_preserved K src dst hK
    intro hl
    have hd := reachable_real_depth K src dst hK S hS p hx
    have hm := (link_midpoint_depth K src dst hK l hl).1
    omega
  · obtain ⟨rfl, rfl⟩ := he
    apply Eq.symm
    apply link_root_preserved K src dst hK
    intro hl
    have hd := reachable_real_depth K src dst hK S hS p hx
    have hm := (link_midpoint_depth K src dst hK l hl).2
    omega

theorem support_walk_root_of_real [DecidableEq E] (K : ℕ) (src dst : E → P)
    (hK : 0 < K) (S : Finset (TypeLink K E)) (hS : S.card ≤ K) (p : P)
    {x y : TypeNode K P E} (w : (typeSupportGraph K src dst S).Walk x y)
    (hx : (typeSupportGraph K src dst S).Reachable (.inl p) x) :
    realRoot K src dst x = realRoot K src dst y := by
  induction w with
  | nil => rfl
  | cons hxy w ih =>
    exact (support_edge_root_of_real K src dst hK S hS p hx hxy).trans
      (ih (hx.trans hxy.reachable))

theorem support_unique_real [DecidableEq E] (K : ℕ) (src dst : E → P)
    (hK : 0 < K) (S : Finset (TypeLink K E)) (hS : S.card ≤ K) {p q : P}
    (h : (typeSupportGraph K src dst S).Reachable (.inl p) (.inl q)) : p = q := by
  obtain ⟨w⟩ := h
  exact support_walk_root_of_real K src dst hK S hS p w (SimpleGraph.Reachable.refl _)

def nodeWire (K : ℕ) : TypeNode K P E → Option E
  | .inl _ => none
  | .inr (e, _) => some e

theorem link_internal_same_wire (K : ℕ) (src dst : E → P) (l : TypeLink K E)
    (hl : ∀ p, linkLeft K src l ≠ Sum.inl p)
    (hr : ∀ p, linkRight K dst l ≠ Sum.inl p) :
    nodeWire K (linkLeft K src l) = nodeWire K (linkRight K dst l) := by
  have h0 : l.2.val ≠ 0 := by
    intro h
    exact hl (src l.1) (dite_eq_left h)
  have h4 : l.2.val ≠ 4 * K := by
    intro h
    exact hr (dst l.1) (dite_eq_left h)
  simp only [linkLeft, linkRight, dite_eq_right h0, dite_eq_right h4, nodeWire]

theorem support_edge_wire (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E))
    {x y : TypeNode K P E} (hxy : (typeSupportGraph K src dst S).Adj x y)
    (hx : ∀ p, x ≠ Sum.inl p) (hy : ∀ p, y ≠ Sum.inl p) :
    nodeWire K x = nodeWire K y := by
  obtain ⟨_, l, _, he | he⟩ := hxy
  · obtain ⟨rfl, rfl⟩ := he
    exact link_internal_same_wire K src dst l hx hy
  · obtain ⟨rfl, rfl⟩ := he
    exact (link_internal_same_wire K src dst l hy hx).symm

theorem support_walk_wire (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E))
    {x y : TypeNode K P E} (w : (typeSupportGraph K src dst S).Walk x y)
    (hreal : ∀ p, ¬(typeSupportGraph K src dst S).Reachable x (.inl p)) :
    nodeWire K x = nodeWire K y := by
  induction w with
  | nil => rfl
  | @cons x z y hxz w ih =>
    have hz : ∀ p, ¬(typeSupportGraph K src dst S).Reachable z (.inl p) :=
      fun p h => hreal p (hxz.reachable.trans h)
    apply (support_edge_wire K src dst S hxz
      (fun p h => hreal p (h ▸ SimpleGraph.Reachable.refl x))
      (fun p h => hz p (h ▸ SimpleGraph.Reachable.refl z))).trans
    exact ih hz

noncomputable def extendCoordinate {Λ : Type uΛ} [Fintype Λ] (A : Finset Λ)
    (f : A → Λ) (hf : Function.Injective f) : Equiv.Perm Λ :=
  Classical.choose (Equiv.Perm.exists_extending_pair Subtype.val f Subtype.val_injective hf)

theorem extendCoordinate_apply {Λ : Type uΛ} [Fintype Λ] (A : Finset Λ)
    (f : A → Λ) (hf : Function.Injective f) (a : A) :
    extendCoordinate A f hf a = f a :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair Subtype.val f Subtype.val_injective hf) a

def typeFrame {Λ : Type uΛ} (K : ℕ) (perm : E → Equiv.Perm Λ) :
    TypeNode K P E → Equiv.Perm Λ
  | .inl _ => Equiv.refl Λ
  | .inr (e, j) => if j.val < 2 * K then Equiv.refl Λ else perm e

def linkMatch {Λ : Type uΛ} (K : ℕ) (perm : E → Equiv.Perm Λ)
    (l : TypeLink K E) : Equiv.Perm Λ :=
  if l.2.val = 4 * K then perm l.1 else Equiv.refl Λ

theorem frame_match {Λ : Type uΛ} (K : ℕ) (src dst : E → P) (hK : 0 < K)
    (perm : E → Equiv.Perm Λ) (l : TypeLink K E) (hmid : l.2.val ≠ 2 * K) (a : Λ) :
    typeFrame K perm (linkLeft K src l) a =
      typeFrame K perm (linkRight K dst l) (linkMatch K perm l a) := by
  have hj := l.2.isLt
  dsimp only [linkLeft, linkRight]
  split_ifs <;> simp only [typeFrame, linkMatch]
  all_goals (try split_ifs) <;> first | rfl | omega

end WLTime.Compression

namespace WLTime.Compression
variable {P : Type uP} {E : Type uE}

theorem support_link_reachable (K : ℕ) (src dst : E → P)
    (S : Finset (TypeLink K E)) {l : TypeLink K E} (hl : l ∈ S) :
    (typeSupportGraph K src dst S).Reachable (linkLeft K src l) (linkRight K dst l) := by
  by_cases h : linkLeft K src l = linkRight K dst l
  · rw [h]
  · exact SimpleGraph.Adj.reachable ⟨h, l, hl, Or.inl ⟨rfl, rfl⟩⟩

def HasReal (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E))
    (t : TypeNode K P E) : Prop :=
  ∃ p, (typeSupportGraph K src dst S).Reachable (Sum.inl p) t

theorem hasReal_of_reachable (K : ℕ) (src dst : E → P)
    (S : Finset (TypeLink K E)) {x y : TypeNode K P E}
    (hxy : (typeSupportGraph K src dst S).Reachable x y) :
    HasReal K src dst S x ↔ HasReal K src dst S y := by
  constructor
  · rintro ⟨p, hp⟩; exact ⟨p, hp.trans hxy⟩
  · rintro ⟨p, hp⟩; exact ⟨p, hp.trans hxy.symm⟩

theorem hasReal_inl (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E)) (p : P) :
    HasReal K src dst S (.inl p) := ⟨p, SimpleGraph.Reachable.refl _⟩

noncomputable def supportFrame {Λ : Type uΛ} (K : ℕ) (src dst : E → P)
    (perm : E → Equiv.Perm Λ) (S : Finset (TypeLink K E)) (t : TypeNode K P E) :
    Equiv.Perm Λ := by
  classical
  exact if HasReal K src dst S t then typeFrame K perm t else Equiv.refl Λ

theorem supportFrame_match [DecidableEq E] {Λ : Type uΛ} (K : ℕ) (src dst : E → P)
    (hK : 0 < K) (perm : E → Equiv.Perm Λ) (S : Finset (TypeLink K E)) (hS : S.card ≤ K)
    (l : TypeLink K E) (hl : l ∈ S) (a : Λ) :
    supportFrame K src dst perm S (linkLeft K src l) a =
      supportFrame K src dst perm S (linkRight K dst l) (linkMatch K perm l a) := by
  classical
  have heq := hasReal_of_reachable K src dst S (support_link_reachable K src dst S hl)
  by_cases hreal : HasReal K src dst S (linkLeft K src l)
  · have hreal' := heq.mp hreal
    simp only [supportFrame, ite_eq_left hreal, ite_eq_left hreal']
    apply frame_match K src dst hK
    intro hmid
    obtain ⟨p, hp⟩ := hreal
    have hd := reachable_real_depth K src dst hK S hS p hp
    have hm := (link_midpoint_depth K src dst hK l hmid).1
    omega
  · have hreal' : ¬HasReal K src dst S (linkRight K dst l) := mt heq.mpr hreal
    have h4 : l.2.val ≠ 4 * K := by
      intro h
      apply hreal'
      simpa only [linkRight, dite_eq_left h] using hasReal_inl K src dst S (dst l.1)
    simp only [supportFrame, ite_eq_right hreal, ite_eq_right hreal', linkMatch, ite_eq_right h4,
      Equiv.refl_apply]

theorem support_graph_mono (K : ℕ) (src dst : E → P)
    {S R : Finset (TypeLink K E)} (h : S ⊆ R) :
    typeSupportGraph K src dst S ≤ typeSupportGraph K src dst R := by
  rintro x y ⟨hne, l, hl, he⟩
  exact ⟨hne, l, h hl, he⟩

end WLTime.Compression

namespace WLTime.Compression
variable {P : Type uP} {E : Type uE} {Λ : Type uΛ}

theorem hasReal_mono (K : ℕ) (src dst : E → P) {S R : Finset (TypeLink K E)}
    (hSR : S ⊆ R) {t : TypeNode K P E} (h : HasReal K src dst S t) : HasReal K src dst R t := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.mono (support_graph_mono K src dst hSR)⟩

theorem realRoot_eq_of_reachable [DecidableEq E] (K : ℕ) (src dst : E → P)
    (hK : 0 < K) (S : Finset (TypeLink K E)) (hS : S.card ≤ K) {p : P} {t : TypeNode K P E}
    (h : (typeSupportGraph K src dst S).Reachable (.inl p) t) : realRoot K src dst t = p := by
  obtain ⟨w⟩ := h
  exact (support_walk_root_of_real K src dst hK S hS p w (SimpleGraph.Reachable.refl _)).symm

theorem root_eq_on_real_component [DecidableEq E] (K : ℕ) (src dst : E → P)
    (hK : 0 < K) (S : Finset (TypeLink K E)) (hS : S.card ≤ K)
    {x y : TypeNode K P E} (hreal : HasReal K src dst S x)
    (hxy : (typeSupportGraph K src dst S).Reachable x y) :
    realRoot K src dst x = realRoot K src dst y := by
  obtain ⟨p, hp⟩ := hreal
  obtain ⟨w⟩ := hxy
  exact support_walk_root_of_real K src dst hK S hS p w hp

theorem frame_eq_on_internal_edge (K : ℕ) (src dst : E → P)
    (perm : E → Equiv.Perm Λ) (S : Finset (TypeLink K E))
    (frame : TypeNode K P E → Equiv.Perm Λ)
    (halign : ∀ l ∈ S, ∀ a, frame (linkLeft K src l) a =
      frame (linkRight K dst l) (linkMatch K perm l a))
    {x y : TypeNode K P E} (hxy : (typeSupportGraph K src dst S).Adj x y)
    (hx : ∀ p, x ≠ Sum.inl p) (hy : ∀ p, y ≠ Sum.inl p) : frame x = frame y := by
  have aux : ∀ l ∈ S, (∀ p, linkRight K dst l ≠ Sum.inl p) →
      frame (linkLeft K src l) = frame (linkRight K dst l) := by
    intro l hl hr
    have h4 : l.2.val ≠ 4*K := by intro h; exact hr (dst l.1) (dite_eq_left h)
    ext a
    simpa only [linkMatch, ite_eq_right h4, Equiv.refl_apply] using halign l hl a
  obtain ⟨_, l, hl, he | he⟩ := hxy
  · obtain ⟨rfl, rfl⟩ := he; exact aux l hl hy
  · obtain ⟨rfl, rfl⟩ := he; exact (aux l hl hx).symm

theorem frame_eq_on_rootfree_walk (K : ℕ) (src dst : E → P)
    (perm : E → Equiv.Perm Λ) (S : Finset (TypeLink K E))
    (frame : TypeNode K P E → Equiv.Perm Λ)
    (halign : ∀ l ∈ S, ∀ a, frame (linkLeft K src l) a =
      frame (linkRight K dst l) (linkMatch K perm l a))
    {x y : TypeNode K P E} (w : (typeSupportGraph K src dst S).Walk x y)
    (hreal : ¬HasReal K src dst S x) : frame x = frame y := by
  induction w with
  | nil => rfl
  | @cons x z y hxz w ih =>
    have hz : ¬HasReal K src dst S z :=
      mt (hasReal_of_reachable K src dst S hxz.reachable).mpr hreal
    apply (frame_eq_on_internal_edge K src dst perm S frame halign hxz
      (fun p he => hreal (he.symm ▸ hasReal_inl K src dst S p))
      (fun p he => hz (he.symm ▸ hasReal_inl K src dst S p))).trans
    exact ih hz

end WLTime.Compression

end OAI
