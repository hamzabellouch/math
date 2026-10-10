import OAI.Computability.WeisfeilerLeman.Consistency

namespace OAI

universe uP uE

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

abbrev RawBlock (K : ℕ) := BlockName r (TypeNode K P E) (TypeLink K E) (Fin m)
abbrev RawCorner (K : ℕ) := Corner r (TypeNode K P E) (Fin m)

noncomputable def drawing (K : ℕ) : BlockDrawing r (RawBlock (r := r) (m := m) (P := P) (E := E) K)
    (RawCorner (r := r) (m := m) (P := P) (E := E) K) :=
  BlockName.drawing (linkLeft K I.src) (linkRight K I.dst)
    (fun l i => linkMatch K (fun e => I.coordinatePerm e i) l)

def LabelAllowed (K : ℕ) : TypeNode K P E → Fin (r+1) → Fin m → Prop
  | .inl _, _, _ => True
  | .inr (e, _), i, a => a ∈ I.domain e i

def ValidBlock (K : ℕ) : RawBlock (r := r) (m := m) (P := P) (E := E) K → Prop
  | .site i t a b => I.LabelAllowed K t i a ∧ I.LabelAllowed K t (finRotate (r+1) i) b
  | .square i l a b => a ∈ I.domain l.1 i ∧ b ∈ I.domain l.1 (finRotate (r+1) i)

theorem linkLeft_allowed (K : ℕ) (l : TypeLink K E) (i : Fin (r+1)) (a : Fin m)
    (ha : a ∈ I.domain l.1 i) : I.LabelAllowed K (linkLeft K I.src l) i a := by
  dsimp only [linkLeft]
  split_ifs <;> simp_all only [LabelAllowed]

theorem linkRight_allowed (K : ℕ) (l : TypeLink K E) (i : Fin (r+1)) (a : Fin m)
    (ha : a ∈ I.domain l.1 i) :
    I.LabelAllowed K (linkRight K I.dst l) i (linkMatch K (fun e => I.coordinatePerm e i) l a) := by
  dsimp only [linkRight]
  split_ifs with h
  · trivial
  · simpa only [LabelAllowed, linkMatch, ite_eq_right h, Equiv.refl_apply] using ha

theorem low_allowed (K : ℕ) (b : RawBlock (r := r) (m := m) (P := P) (E := E) K)
    (hb : I.ValidBlock K b) (s : Bool) :
    I.LabelAllowed K ((I.drawing K).low b s).type ((I.drawing K).low b s).boundary
      ((I.drawing K).low b s).label := by
  cases b with
  | site i t a b => exact hb.1
  | square i l a b =>
    cases s
    · exact I.linkLeft_allowed K l i a hb.1
    · exact I.linkRight_allowed K l i a hb.1

theorem high_allowed (K : ℕ) (b : RawBlock (r := r) (m := m) (P := P) (E := E) K)
    (hb : I.ValidBlock K b) (s : Bool) :
    I.LabelAllowed K ((I.drawing K).high b s).type ((I.drawing K).high b s).boundary
      ((I.drawing K).high b s).label := by
  cases b with
  | site i t a b => exact hb.2
  | square i l a b =>
    cases s
    · exact I.linkLeft_allowed K l _ b hb.2
    · exact I.linkRight_allowed K l _ b hb.2

noncomputable def alignedLabel [DecidableEq E] (K : ℕ)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (c : RawCorner (r := r) (m := m) (P := P) (E := E) K) : Fin m :=
  supportFrame K I.src I.dst (fun e => I.coordinatePerm e c.boundary)
    (BlockName.links U) c.type c.label

theorem alignedLabel_sides [DecidableEq E] (K : ℕ) (hK : 0 < K)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (hU : U.card ≤ K) :
    ∀ b ∈ U, I.alignedLabel K U ((I.drawing K).low b false) =
        I.alignedLabel K U ((I.drawing K).low b true) ∧
      I.alignedLabel K U ((I.drawing K).high b false) =
        I.alignedLabel K U ((I.drawing K).high b true) := by
  exact BlockName.drawing_aligned (linkLeft K I.src) (linkRight K I.dst)
    (fun l i => linkMatch K (fun e => I.coordinatePerm e i) l)
    (fun t i => supportFrame K I.src I.dst (fun e => I.coordinatePerm e i) (BlockName.links U) t) U
    (fun _ l _ _ hb _ p => supportFrame_match K I.src I.dst hK _ _
      ((BlockName.links_card U).trans hU) l (BlockName.square_link_mem hb) p)

theorem corner_type_reachable [DecidableEq E] (K : ℕ)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    {x y : RawCorner (r := r) (m := m) (P := P) (E := E) K}
    (h : ((I.drawing K).graph U).Reachable x y) :
    (typeSupportGraph K I.src I.dst (BlockName.links U)).Reachable x.type y.type := by
  apply (I.drawing K).map_reachable U _ Corner.type _ _ _ h
  · intro b _ s; cases b <;> cases s <;> rfl
  · intro b hb
    cases b with
    | site => exact SimpleGraph.Reachable.refl _
    | square => exact support_link_reachable K I.src I.dst _ (BlockName.square_link_mem hb)
  · intro b hb
    cases b with
    | site => exact SimpleGraph.Reachable.refl _
    | square => exact support_link_reachable K I.src I.dst _ (BlockName.square_link_mem hb)

structure WrapData [DecidableEq E] (K : ℕ)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) where
  blocks : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)
  subset : blocks ⊆ U
  card : blocks.card = r+1
  wraps : (I.drawing K).Wraps blocks
  address : I.Address
  reads : ∀ b ∈ blocks, ∀ s,
    I.alignedLabel K U ((I.drawing K).low b s) = address ((I.drawing K).row b) ∧
    I.alignedLabel K U ((I.drawing K).high b s) = address (finRotate (r+1) ((I.drawing K).row b))
  anchor : RawBlock (r := r) (m := m) (P := P) (E := E) K
  anchor_mem : anchor ∈ blocks

theorem wrapData_exists [DecidableEq E] (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r)
    (U A : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (hU : U.card ≤ K) (hA : A ⊆ U) (hc : A.card = r+1) (hw : (I.drawing K).Wraps A) :
    Nonempty (I.WrapData K U) := by
  obtain ⟨a, ha⟩ := (I.drawing K).address_exists hr A (I.alignedLabel K U)
    (fun b hb => I.alignedLabel_sides K hK U hU b (hA hb)) hw hc
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  exact ⟨⟨A, hA, hc, hw, a, ha, b, hb⟩⟩

namespace WrapData
variable [DecidableEq E] {I} {K : ℕ}
    {U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}

noncomputable abbrev rootType (d : I.WrapData K U) : TypeNode K P E := ((I.drawing K).low d.anchor false).type

theorem address_unique [DecidableEq P] (hr : 2 ≤ r) (hU : U.card ≤ r+2)
    (d f : I.WrapData K U) : d.address = f.address :=
  (I.drawing K).addresses_agree hr U d.blocks f.blocks d.subset f.subset hU
    d.wraps d.card f.card (I.alignedLabel K U) d.address f.address d.reads f.reads

theorem type_reachable (hr : 2 ≤ r) (d : I.WrapData K U)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ d.blocks) (s : Bool) :
    (typeSupportGraph K I.src I.dst (BlockName.links U)).Reachable d.rootType
      ((I.drawing K).low b s).type := by
  apply I.corner_type_reachable K U
  apply SimpleGraph.Reachable.mono ((I.drawing K).graph_mono d.subset)
  exact ((I.drawing K).wraps_connected hr d.blocks d.wraps d.card d.anchor d.anchor_mem b hb).trans
    ((I.drawing K).low_reachable d.blocks hb s)

theorem rootfree_allowed (hr : 2 ≤ r) (d : I.WrapData K U)
    (hvalid : ∀ b ∈ U, I.ValidBlock K b) (e : E) (j : Fin (4*K))
    (he : d.rootType = .inr (e,j))
    (hreal : ¬HasReal K I.src I.dst (BlockName.links U) d.rootType) :
    I.Allowed e d.address := by
  intro i
  obtain ⟨b, ⟨hb, hrow⟩, _⟩ := (I.drawing K).wraps_unique_row hr d.blocks d.wraps d.card i
  have hrch := d.type_reachable hr b hb false
  have hreal' : ¬HasReal K I.src I.dst (BlockName.links U) ((I.drawing K).low b false).type :=
    mt (hasReal_of_reachable K I.src I.dst _ hrch).mpr hreal
  have hw : nodeWire K d.rootType = nodeWire K ((I.drawing K).low b false).type := by
    obtain ⟨w⟩ := hrch
    exact support_walk_wire K I.src I.dst _ w (fun p h => hreal ⟨p, h.symm⟩)
  have hallowed := I.low_allowed K b (hvalid b (d.subset hb)) false
  have hlabel := (d.reads b hb false).1
  simp only [alignedLabel, supportFrame, ite_eq_right hreal', Equiv.refl_apply] at hlabel
  have hboundary := (I.drawing K).low_boundary b false
  rw [hrow] at hboundary
  change ((I.drawing K).low b false).boundary = i at hboundary
  rw [hrow] at hlabel
  rw [he] at hw
  cases ht : ((I.drawing K).low b false).type with
  | inl p =>
    simp only [ht, nodeWire] at hw
    contradiction
  | inr ej =>
    rcases ej with ⟨e',j'⟩
    simp only [ht, nodeWire, Option.some.injEq] at hw
    subst e'
    simpa only [ht, LabelAllowed, hlabel, hboundary] using hallowed

omit [DecidableEq E] in

theorem type_low_high (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (s : Bool) :
    ((I.drawing K).low b s).type = ((I.drawing K).high b s).type := by
  cases b <;> cases s <;> rfl

theorem type_reachable_blocks (hr : 2 ≤ r) (d : I.WrapData K U)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ d.blocks) (s : Bool) :
    (typeSupportGraph K I.src I.dst (BlockName.links d.blocks)).Reachable d.rootType
      ((I.drawing K).low b s).type := by
  apply I.corner_type_reachable K d.blocks
  exact ((I.drawing K).wraps_connected hr d.blocks d.wraps d.card d.anchor d.anchor_mem b hb).trans
    ((I.drawing K).low_reachable d.blocks hb s)

noncomputable def changedAddress (d : I.WrapData K U)
    (W : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) : I.Address :=
  fun i => frameTransition
    (supportFrame K I.src I.dst (fun e => I.coordinatePerm e i) (BlockName.links U))
    (supportFrame K I.src I.dst (fun e => I.coordinatePerm e i) (BlockName.links W))
    d.rootType (d.address i)

theorem changedAddress_reads (hK : 0 < K) (hr : 2 ≤ r) (d : I.WrapData K U)
    (W : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (hU : U.card ≤ K) (hW : W.card ≤ K) (hdW : d.blocks ⊆ W)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ d.blocks) (s : Bool) :
    I.alignedLabel K W ((I.drawing K).low b s) = d.changedAddress W ((I.drawing K).row b) ∧
    I.alignedLabel K W ((I.drawing K).high b s) =
      d.changedAddress W (finRotate (r+1) ((I.drawing K).row b)) := by
  have aux (c : RawCorner (r := r) (m := m) (P := P) (E := E) K)
      (hc : (typeSupportGraph K I.src I.dst (BlockName.links d.blocks)).Reachable d.rootType c.type) :
      I.alignedLabel K W c = frameTransition
        (supportFrame K I.src I.dst (fun e => I.coordinatePerm e c.boundary) (BlockName.links U))
        (supportFrame K I.src I.dst (fun e => I.coordinatePerm e c.boundary) (BlockName.links W))
        d.rootType (I.alignedLabel K U c) := by
    obtain ⟨w⟩ := hc
    have heq := frameTransition_walk K I.src I.dst (fun e => I.coordinatePerm e c.boundary)
      (BlockName.links d.blocks)
      (supportFrame K I.src I.dst (fun e => I.coordinatePerm e c.boundary) (BlockName.links U))
      (supportFrame K I.src I.dst (fun e => I.coordinatePerm e c.boundary) (BlockName.links W))
      (fun l hl a => supportFrame_match K I.src I.dst hK _ _ ((BlockName.links_card U).trans hU)
        l (BlockName.links_mono d.subset hl) a)
      (fun l hl a => supportFrame_match K I.src I.dst hK _ _ ((BlockName.links_card W).trans hW)
        l (BlockName.links_mono hdW hl) a) w
    rw [heq]
    simp only [frameTransition, Equiv.trans_apply, alignedLabel, Equiv.symm_apply_apply]
  have hlo := aux ((I.drawing K).low b s) (d.type_reachable_blocks hr b hb s)
  have hhi := aux ((I.drawing K).high b s)
    ((type_low_high (I := I) b s) ▸ d.type_reachable_blocks hr b hb s)
  have hbl : ((I.drawing K).low b s).boundary = ((I.drawing K).row b) :=
    (I.drawing K).low_boundary b s
  have hbh : ((I.drawing K).high b s).boundary = finRotate (r+1) ((I.drawing K).row b) :=
    (I.drawing K).high_boundary b s
  rw [(d.reads b hb s).1, hbl] at hlo
  rw [(d.reads b hb s).2, hbh] at hhi
  exact ⟨hlo, hhi⟩

noncomputable def reframe (hK : 0 < K) (hr : 2 ≤ r) (d : I.WrapData K U)
    (W : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (hU : U.card ≤ K) (hW : W.card ≤ K) (hdW : d.blocks ⊆ W) : I.WrapData K W where
  blocks := d.blocks
  subset := hdW
  card := d.card
  wraps := d.wraps
  address := d.changedAddress W
  reads := d.changedAddress_reads hK hr W hU hW hdW
  anchor := d.anchor
  anchor_mem := d.anchor_mem

theorem roots_connected [DecidableEq P] (hr : 2 ≤ r) (hU : U.card ≤ r+2)
    (d f : I.WrapData K U) :
    (typeSupportGraph K I.src I.dst (BlockName.links U)).Reachable d.rootType f.rootType := by
  classical
  have hne : (d.blocks ∩ f.blocks).Nonempty := by
    by_contra h
    have hz := Finset.not_nonempty_iff_eq_empty.mp h
    have hc := Finset.card_union_add_card_inter d.blocks f.blocks
    have hsub : d.blocks ∪ f.blocks ⊆ U := Finset.union_subset d.subset f.subset
    have hle := Finset.card_le_card hsub
    rw [hz, Finset.card_empty, d.card, f.card] at hc
    omega
  obtain ⟨b, hb⟩ := hne
  exact (d.type_reachable hr b (Finset.mem_inter.mp hb).1 false).trans
    (f.type_reachable hr b (Finset.mem_inter.mp hb).2 false).symm

end WrapData
end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

structure ShiftChoice where
  real : (p : P) → I.RealValue p
  scalar : E → F₂

namespace ShiftChoice
variable {I}
noncomputable def values (q : I.ShiftChoice) (K : ℕ) (S : Finset (TypeLink K E)) :=
  I.canonicalShift K S q.real q.scalar

def AtAddress (q : I.ShiftChoice) (Q : I.ArcWitness) (a : I.Address) : Prop :=
  (∀ p, q.real p ∈ Q.sets p a) ∧ (∀ e, q.scalar e ∈ Q.internalSet e a)

noncomputable def atAddress (Q : I.ArcWitness) (a : I.Address) : I.ShiftChoice where
  real := fun p => (Q.nonempty p a).choose
  scalar := fun e => (Q.internal_nonempty e a).choose

theorem atAddress_mem (Q : I.ArcWitness) (a : I.Address) :
    (atAddress Q a).AtAddress Q a :=
  ⟨fun p => (Q.nonempty p a).choose_spec, fun e => (Q.internal_nonempty e a).choose_spec⟩

noncomputable def withReal [DecidableEq P] (q : I.ShiftChoice) (p : P) (h : I.RealValue p) :
    I.ShiftChoice := ⟨Function.update q.real p h, q.scalar⟩

noncomputable def withScalar [DecidableEq E] (q : I.ShiftChoice) (e : E) (s : F₂) :
    I.ShiftChoice := ⟨q.real, Function.update q.scalar e s⟩

theorem withReal_mem [DecidableEq P] (q : I.ShiftChoice) (Q : I.ArcWitness) (a : I.Address)
    (hq : q.AtAddress Q a) (p : P) (h : I.RealValue p) (hh : h ∈ Q.sets p a) :
    (q.withReal p h).AtAddress Q a := by
  constructor
  · intro t
    by_cases ht : t = p
    · subst t; simpa only [withReal, Function.update_self] using hh
    · simpa only [withReal, Function.update_of_ne ht] using hq.1 t
  · exact hq.2

theorem withScalar_mem [DecidableEq E] (q : I.ShiftChoice) (Q : I.ArcWitness) (a : I.Address)
    (hq : q.AtAddress Q a) (e : E) (s : F₂) (hs : s ∈ Q.internalSet e a) :
    (q.withScalar e s).AtAddress Q a := by
  constructor
  · exact hq.1
  · intro t
    by_cases ht : t = e
    · subst t; simpa only [withScalar, Function.update_self] using hs
    · simpa only [withScalar, Function.update_of_ne ht] using hq.2 t

def Admissible [DecidableEq E] (q : I.ShiftChoice) (Q : I.ArcWitness) (K : ℕ)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) : Prop :=
  ∀ d : I.WrapData K U, q.AtAddress Q d.address

theorem admissible_of_one [DecidableEq P] [DecidableEq E]
    (q : I.ShiftChoice) (Q : I.ArcWitness) (K : ℕ) (hr : 2 ≤ r)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (hU : U.card ≤ r+2)
    (d : I.WrapData K U) (hq : q.AtAddress Q d.address) : q.Admissible Q K U := by
  intro f
  rw [← d.address_unique hr hU f]
  exact hq

theorem admissible_exists [DecidableEq P] [DecidableEq E] (Q : I.ArcWitness)
    (K : ℕ) (hr : 2 ≤ r)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (hU : U.card ≤ r+2) :
    ∃ q : I.ShiftChoice, q.Admissible Q K U := by
  classical
  by_cases h : Nonempty (I.WrapData K U)
  · obtain ⟨d⟩ := h
    exact ⟨atAddress Q d.address, admissible_of_one _ Q K hr U hU d (atAddress_mem Q _)⟩
  · exact ⟨⟨fun _ => 0, fun _ => 0⟩, fun d => False.elim (h ⟨d⟩)⟩

end ShiftChoice

namespace WrapData
variable [DecidableEq E] {I} {K : ℕ}
    {U W : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}

theorem changedAddress_both_real (d : I.WrapData K U)
    (h : HasReal K I.src I.dst (BlockName.links U) d.rootType)
    (h' : HasReal K I.src I.dst (BlockName.links W) d.rootType) :
    d.changedAddress W = d.address := by
  funext i
  simp only [changedAddress, frameTransition, supportFrame, ite_eq_left h, ite_eq_left h',
    Equiv.trans_apply, Equiv.apply_symm_apply]

theorem changedAddress_neither_real (d : I.WrapData K U)
    (h : ¬HasReal K I.src I.dst (BlockName.links U) d.rootType)
    (h' : ¬HasReal K I.src I.dst (BlockName.links W) d.rootType) :
    d.changedAddress W = d.address := by
  funext i
  simp only [changedAddress, frameTransition, supportFrame, ite_eq_right h, ite_eq_right h',
    Equiv.trans_apply, Equiv.apply_symm_apply]

theorem changedAddress_new_real (d : I.WrapData K U)
    (h : ¬HasReal K I.src I.dst (BlockName.links U) d.rootType)
    (h' : HasReal K I.src I.dst (BlockName.links W) d.rootType)
    (e : E) (j : Fin (4*K)) (he : d.rootType = .inr (e,j)) :
    d.changedAddress W = if j.val < 2*K then d.address else I.permuteAddress e d.address := by
  funext i
  simp only [changedAddress, frameTransition, supportFrame, ite_eq_right h, ite_eq_left h',
    Equiv.trans_apply, Equiv.refl_symm, Equiv.refl_apply, he, typeFrame]
  split_ifs <;> rfl

end WrapData

theorem shifts_eq_on_rootfree_component (K : ℕ) (S : Finset (TypeLink K E))
    (h g : (t : TypeNode K P E) → I.Value K t)
    (hh : I.ShiftSolves K S h) (hg : I.ShiftSolves K S g)
    {x y : TypeNode K P E}
    (hreal : ¬HasReal K I.src I.dst S x)
    (hxy : (typeSupportGraph K I.src I.dst S).Reachable x y) (heq : h x = g x) : h y = g y := by
  have hy : ¬HasReal K I.src I.dst S y := mt (hasReal_of_reachable K I.src I.dst S hxy).mpr hreal
  obtain ⟨w⟩ := hxy
  have hxscalar : I.scalarOf K h x = I.scalarOf K g x := by
    cases x with
    | inl p => exact (hreal (hasReal_inl K I.src I.dst S p)).elim
    | inr ej => exact heq
  have hyscalar := (I.scalar_eq_on_rootfree_walk K S h hh w hreal).symm.trans
    (hxscalar.trans (I.scalar_eq_on_rootfree_walk K S g hg w hreal))
  cases y with
  | inl p => exact (hy (hasReal_inl K I.src I.dst S p)).elim
  | inr ej => exact hyscalar

namespace ShiftChoice
variable {I}

open scoped Classical in
theorem values_internal (q : I.ShiftChoice) (K : ℕ) (S : Finset (TypeLink K E))
    (e : E) (j : Fin (4*K)) :
    q.values K S (.inr (e,j)) =
      if HasReal K I.src I.dst S (.inr (e,j)) then
        (if j.val < 2*K then I.affineSrc e (q.real (I.src e)) else I.affineDst e (q.real (I.dst e)))
      else q.scalar e := by
  classical
  rfl

theorem values_solves [DecidableEq E] (q : I.ShiftChoice) (K : ℕ) (hK : 0 < K)
    (S : Finset (TypeLink K E)) (hS : S.card ≤ K) : I.ShiftSolves K S (q.values K S) :=
  I.canonicalShift_solves K hK S hS q.real q.scalar

theorem newly_rooted_preimage [DecidableEq E] [DecidableEq P]
    (Q : I.ArcWitness) (K : ℕ) (hr : 2 ≤ r)
    {V U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    (d : I.WrapData K V) (hvalid : ∀ b ∈ V, I.ValidBlock K b)
    (hV : ¬HasReal K I.src I.dst (BlockName.links V) d.rootType)
    (hU : HasReal K I.src I.dst (BlockName.links U) d.rootType)
    (e : E) (j : Fin (4*K)) (he : d.rootType = .inr (e,j))
    (s : F₂) (hs : s ∈ Q.internalSet e d.address) :
    ∃ q : I.ShiftChoice, q.AtAddress Q (d.changedAddress U) ∧
      q.values K (BlockName.links U) (.inr (e,j)) = s := by
  classical
  have ha := d.changedAddress_new_real hV hU e j he
  have hU' : HasReal K I.src I.dst (BlockName.links U) (.inr (e,j)) := he ▸ hU
  by_cases hj : j.val < 2*K
  · rw [ite_eq_left hj] at ha
    obtain ⟨x, hx, hxs⟩ := Q.src_preimage e d.address hs
    let q := (atAddress Q (d.changedAddress U)).withReal (I.src e) x
    refine ⟨q, withReal_mem _ _ _ (atAddress_mem _ _) _ _ ?_, ?_⟩
    · rwa [ha]
    · rw [q.values_internal, ite_eq_left hU', ite_eq_left hj]
      simpa only [q, withReal, Function.update_self] using hxs
  · rw [ite_eq_right hj] at ha
    obtain ⟨x, hx, hxs⟩ := Q.dst_preimage e d.address (d.rootfree_allowed hr hvalid e j he hV) hs
    let q := (atAddress Q (d.changedAddress U)).withReal (I.dst e) x
    refine ⟨q, withReal_mem _ _ _ (atAddress_mem _ _) _ _ ?_, ?_⟩
    · rwa [ha]
    · rw [q.values_internal, ite_eq_left hU', ite_eq_right hj]
      simpa only [q, withReal, Function.update_self] using hxs

theorem newly_rooted_image [DecidableEq E]
    (Q : I.ArcWitness) (K : ℕ) (hr : 2 ≤ r)
    {V U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    (d : I.WrapData K V) (hvalid : ∀ b ∈ V, I.ValidBlock K b)
    (hV : ¬HasReal K I.src I.dst (BlockName.links V) d.rootType)
    (hU : HasReal K I.src I.dst (BlockName.links U) d.rootType)
    (e : E) (j : Fin (4*K)) (he : d.rootType = .inr (e,j))
    (q : I.ShiftChoice) (hq : q.AtAddress Q (d.changedAddress U)) :
    q.values K (BlockName.links U) (.inr (e,j)) ∈ Q.internalSet e d.address := by
  have ha := d.changedAddress_new_real hV hU e j he
  have hU' : HasReal K I.src I.dst (BlockName.links U) (.inr (e,j)) := he ▸ hU
  rw [q.values_internal, ite_eq_left hU']
  by_cases hj : j.val < 2*K
  · rw [ite_eq_left hj] at ha ⊢
    apply Q.src_mem_internal e d.address
    rw [← ha]
    exact hq.1 _
  · rw [ite_eq_right hj] at ha ⊢
    apply Q.dst_mem_internal e d.address (d.rootfree_allowed hr hvalid e j he hV)
    rw [← ha]
    exact hq.1 _

theorem extend_on_wrapping [DecidableEq E] [DecidableEq P]
    (Q : I.ArcWitness) (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r)
    {V U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    (hVU : V ⊆ U) (hUK : U.card ≤ K) (hUr : U.card ≤ r+2)
    (d : I.WrapData K V) (hvalid : ∀ b ∈ V, I.ValidBlock K b)
    (q : I.ShiftChoice) (hq : q.Admissible Q K V) :
    ∃ q' : I.ShiftChoice, q'.Admissible Q K U ∧
      ∀ t, (typeSupportGraph K I.src I.dst (BlockName.links V)).Reachable d.rootType t →
        q'.values K (BlockName.links U) t = q.values K (BlockName.links V) t := by
  classical
  have hVK : V.card ≤ K := (Finset.card_le_card hVU).trans hUK
  let f := d.reframe hK hr U hVK hUK (d.subset.trans hVU)
  have hqAt := hq d
  have hsub := BlockName.links_mono hVU
  by_cases hVr : HasReal K I.src I.dst (BlockName.links V) d.rootType
  · have hUrt := hasReal_mono K I.src I.dst hsub hVr
    have ha := d.changedAddress_both_real hVr hUrt
    refine ⟨q, admissible_of_one q Q K hr U hUr f ?_, ?_⟩
    · change q.AtAddress Q (d.changedAddress U)
      rwa [ha]
    · intro t ht
      have htV := (hasReal_of_reachable K I.src I.dst _ ht).mp hVr
      have htU := hasReal_mono K I.src I.dst hsub htV
      simp only [values, canonicalShift, ite_eq_left htV, ite_eq_left htU]
  · by_cases hUr' : HasReal K I.src I.dst (BlockName.links U) d.rootType
    · obtain ⟨e,j,he⟩ : ∃ e j, d.rootType = Sum.inr (e,j) := by
        cases he : d.rootType with
        | inl p => exact (hVr (he.symm ▸ hasReal_inl K I.src I.dst _ p)).elim
        | inr ej => exact ⟨ej.1, ej.2, rfl⟩
      obtain ⟨q', hq', heq⟩ := newly_rooted_preimage Q K hr d hvalid hVr hUr'
        e j he (q.scalar e) (hqAt.2 e)
      refine ⟨q', admissible_of_one q' Q K hr U hUr f hq', ?_⟩
      intro t ht
      apply I.shifts_eq_on_rootfree_component K (BlockName.links V)
        (q'.values K (BlockName.links U)) (q.values K (BlockName.links V))
        (fun l hl => q'.values_solves K hK _ ((BlockName.links_card U).trans hUK) l (hsub hl))
        (q.values_solves K hK _ ((BlockName.links_card V).trans hVK)) hVr ht
      have hVr' : ¬HasReal K I.src I.dst (BlockName.links V) (.inr (e,j)) := he ▸ hVr
      rw [he, q.values_internal, ite_eq_right hVr']
      exact heq
    · have ha := d.changedAddress_neither_real hVr hUr'
      refine ⟨q, admissible_of_one q Q K hr U hUr f ?_, ?_⟩
      · change q.AtAddress Q (d.changedAddress U)
        rwa [ha]
      · intro t ht
        have htV : ¬HasReal K I.src I.dst (BlockName.links V) t :=
          mt (hasReal_of_reachable K I.src I.dst _ ht).mpr hVr
        have htU : ¬HasReal K I.src I.dst (BlockName.links U) t :=
          mt (hasReal_of_reachable K I.src I.dst _ (ht.mono (support_graph_mono K I.src I.dst hsub))).mpr hUr'
        simp only [values, canonicalShift, ite_eq_right htV, ite_eq_right htU]

theorem restrict_on_wrapping [DecidableEq E] [DecidableEq P]
    (Q : I.ArcWitness) (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r)
    {V U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    (hVU : V ⊆ U) (hUK : U.card ≤ K) (hVr : V.card ≤ r+2)
    (d : I.WrapData K V) (hvalid : ∀ b ∈ V, I.ValidBlock K b)
    (q : I.ShiftChoice) (hq : q.Admissible Q K U) :
    ∃ q' : I.ShiftChoice, q'.Admissible Q K V ∧
      ∀ t, (typeSupportGraph K I.src I.dst (BlockName.links V)).Reachable d.rootType t →
        q'.values K (BlockName.links V) t = q.values K (BlockName.links U) t := by
  classical
  have hVK : V.card ≤ K := (Finset.card_le_card hVU).trans hUK
  let f := d.reframe hK hr U hVK hUK (d.subset.trans hVU)
  have hqAt : q.AtAddress Q (d.changedAddress U) := hq f
  have hsub := BlockName.links_mono hVU
  by_cases hVreal : HasReal K I.src I.dst (BlockName.links V) d.rootType
  · have hUrt := hasReal_mono K I.src I.dst hsub hVreal
    have ha := d.changedAddress_both_real hVreal hUrt
    refine ⟨q, admissible_of_one q Q K hr V hVr d ?_, ?_⟩
    · rwa [ha] at hqAt
    · intro t ht
      have htV := (hasReal_of_reachable K I.src I.dst _ ht).mp hVreal
      have htU := hasReal_mono K I.src I.dst hsub htV
      simp only [values, canonicalShift, ite_eq_left htV, ite_eq_left htU]
  · by_cases hUr' : HasReal K I.src I.dst (BlockName.links U) d.rootType
    · obtain ⟨e,j,he⟩ : ∃ e j, d.rootType = Sum.inr (e,j) := by
        cases he : d.rootType with
        | inl p => exact (hVreal (he.symm ▸ hasReal_inl K I.src I.dst _ p)).elim
        | inr ej => exact ⟨ej.1, ej.2, rfl⟩
      let s := q.values K (BlockName.links U) (.inr (e,j))
      have hs : s ∈ Q.internalSet e d.address := newly_rooted_image Q K hr d hvalid hVreal hUr' e j he q hqAt
      let q' := (atAddress Q d.address).withScalar e s
      have hq' := withScalar_mem _ Q d.address (atAddress_mem Q _) e s hs
      refine ⟨q', admissible_of_one q' Q K hr V hVr d hq', ?_⟩
      intro t ht
      apply I.shifts_eq_on_rootfree_component K (BlockName.links V)
        (q'.values K (BlockName.links V)) (q.values K (BlockName.links U))
        (q'.values_solves K hK _ ((BlockName.links_card V).trans hVK))
        (fun l hl => q.values_solves K hK _ ((BlockName.links_card U).trans hUK) l (hsub hl)) hVreal ht
      have hVr' : ¬HasReal K I.src I.dst (BlockName.links V) (.inr (e,j)) := he ▸ hVreal
      rw [he, q'.values_internal, ite_eq_right hVr']
      exact Function.update_self e s (atAddress Q d.address).scalar
    · have ha := d.changedAddress_neither_real hVreal hUr'
      refine ⟨q, admissible_of_one q Q K hr V hVr d ?_, ?_⟩
      · rwa [ha] at hqAt
      · intro t ht
        have htV : ¬HasReal K I.src I.dst (BlockName.links V) t :=
          mt (hasReal_of_reachable K I.src I.dst _ ht).mpr hVreal
        have htU : ¬HasReal K I.src I.dst (BlockName.links U) t :=
          mt (hasReal_of_reachable K I.src I.dst _ (ht.mono (support_graph_mono K I.src I.dst hsub))).mpr hUr'
        simp only [values, canonicalShift, ite_eq_right htV, ite_eq_right htU]

end ShiftChoice
end ConsistencyData
end WLTime.Compression

end OAI
