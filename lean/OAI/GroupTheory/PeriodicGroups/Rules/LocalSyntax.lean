import Mathlib

namespace OAI

section
universe u v w

namespace SourceBurnside.LocalSyntax

inductive Marker
  | idle | left | boundary | full | right
  deriving DecidableEq

inductive Position (q : ℕ)
  | core (p : Fin q)
  | palette (color : Fin q)
  | stop
  deriving DecidableEq

structure Metadata (k : ℕ) where
  arity : Fin k
  zeroTask : Bool
  block : Fin (arity.val + 1)
  deriving DecidableEq

structure Skeleton (q k : ℕ) where
  pos : Position q
  marker : Marker
  metadata : Metadata k
  deriving DecidableEq

namespace Skeleton
variable {q k : ℕ}

def first (c : Skeleton q k) : Prop := c.metadata.block.val = 0 ∧
  ∃ p, c.pos = .core p ∧ p.val = 0

def last (c : Skeleton q k) : Prop :=
  c.metadata.block.val = c.metadata.arity.val ∧ c.pos = .stop

def Admissible (c : Skeleton q k) : Prop :=
  (c.marker = .right → ¬ c.first) ∧ (c.marker = .left → ¬ c.last)

def leftExternal (c : Skeleton q k) : Prop :=
  c.marker = .idle ∨ (c.marker ≠ .right ∧ c.first)

def rightExternal (c : Skeleton q k) : Prop :=
  c.marker = .idle ∨ c.marker = .boundary ∨ (c.marker ≠ .left ∧ c.last)

def acceptsLeft (c : Skeleton q k) (m : Marker) : Prop :=
  if c.marker = .right then m = .full ∨ m = .right else m = .left

def acceptsRight (c : Skeleton q k) (m : Marker) : Prop :=
  if c.marker = .left then m = .left ∨ m = .boundary ∨ m = .full else m = .right

def Structural (a b : Skeleton q k) : Prop :=
  match a.pos, b.pos with
  | .core p, .core r => p.val + 1 = r.val
  | .core p, .palette _ => p.val + 1 = q
  | .palette _, .palette _ => True
  | .palette _, .stop => True
  | .stop, .core r => r.val = 0
  | _, _ => False

def Internal (a b : Skeleton q k) : Prop :=
  a.metadata.arity = b.metadata.arity ∧ a.metadata.zeroTask = b.metadata.zeroTask ∧
  (if a.pos = .stop then a.metadata.block.val + 1 = b.metadata.block.val
     else a.metadata.block.val = b.metadata.block.val) ∧ ¬ b.first ∧ ¬ a.last

def Pair (a b : Skeleton q k) : Prop :=
  Structural a b ∧
    ((a.rightExternal ∧ b.leftExternal) ∨
      (¬ a.rightExternal ∧ ¬ b.leftExternal ∧
        a.acceptsRight b.marker ∧ b.acceptsLeft a.marker ∧ Internal a b))

def mark (c : Skeleton q k) (m : Marker) : Skeleton q k := { c with marker := m }

@[simp] lemma mark_first (c : Skeleton q k) (m : Marker) : (c.mark m).first ↔ c.first := Iff.rfl
@[simp] lemma mark_last (c : Skeleton q k) (m : Marker) : (c.mark m).last ↔ c.last := Iff.rfl
@[simp] lemma mark_pos (c : Skeleton q k) (m : Marker) : (c.mark m).pos = c.pos := rfl
@[simp] lemma mark_metadata (c : Skeleton q k) (m : Marker) :
    (c.mark m).metadata = c.metadata := rfl
@[simp] lemma mark_marker (c : Skeleton q k) (m : Marker) :
    (c.mark m).marker = m := rfl

lemma structural_mark_left (a b : Skeleton q k) (m : Marker) :
    Structural (a.mark m) b ↔ Structural a b := Iff.rfl
lemma structural_mark_right (a b : Skeleton q k) (m : Marker) :
    Structural a (b.mark m) ↔ Structural a b := Iff.rfl
lemma internal_mark_left (a b : Skeleton q k) (m : Marker) :
    Internal (a.mark m) b ↔ Internal a b := Iff.rfl
lemma internal_mark_right (a b : Skeleton q k) (m : Marker) :
    Internal a (b.mark m) ↔ Internal a b := Iff.rfl

lemma left_wing_head (a b : Skeleton q k) (m : Marker)
    (hm : m = .left ∨ m = .boundary ∨ m = .full) :
    Pair a (b.mark m) ↔ Pair a (b.mark .left) := by
  rcases hm with rfl | rfl | rfl <;>
    cases h : a.marker <;>
    simp [Pair, structural_mark_right, internal_mark_right, leftExternal,
      rightExternal, acceptsLeft, acceptsRight, h]

lemma right_wing_head (a b : Skeleton q k) :
    Pair (a.mark .full) b ↔ Pair (a.mark .right) b := by
  cases h : b.marker <;>
    simp [Pair, structural_mark_left, internal_mark_left, leftExternal,
      rightExternal, acceptsLeft, acceptsRight, h]

lemma cursor_left (a b : Skeleton q k) :
    Pair a (b.mark .boundary) ↔ Pair a (b.mark .left) :=
  left_wing_head a b _ (Or.inr (Or.inl rfl))

lemma cursor_right (a b : Skeleton q k) :
    Pair (a.mark .boundary) b ↔ Pair (a.mark .idle) b := by
  simp [Pair, structural_mark_left, internal_mark_left, leftExternal,
    rightExternal, acceptsLeft, acceptsRight]

lemma create_left (a b : Skeleton q k) (hb : b.first) :
    Pair a (b.mark .boundary) ↔ Pair a (b.mark .idle) := by
  simp [Pair, structural_mark_right, internal_mark_right, leftExternal,
    rightExternal, acceptsLeft, acceptsRight, hb]

lemma finish_right (a b : Skeleton q k) (ha : a.last) :
    Pair (a.mark .boundary) b ↔ Pair (a.mark .full) b := by
  simp [Pair, structural_mark_left, internal_mark_left, leftExternal,
    rightExternal, acceptsLeft, acceptsRight, ha]

lemma full_move_pair (a b : Skeleton q k) :
    Pair (a.mark .full) (b.mark .right) ↔
      Pair (a.mark .left) (b.mark .full) := by
  simp only [Pair, structural_mark_left, structural_mark_right, rightExternal,
    leftExternal, mark_marker, mark_last, mark_first, acceptsRight, acceptsLeft,
    internal_mark_left, internal_mark_right]
  simp
  unfold Internal
  tauto

def Link : Option (Skeleton q k) → Option (Skeleton q k) → Prop
  | none, none => True
  | none, some b => b.leftExternal
  | some a, none => a.rightExternal
  | some a, some b => Pair a b

def Closed (w : List (Skeleton q k)) : Prop :=
  (∀ c ∈ w, c.Admissible) ∧
    List.IsChain Link (none :: (w.map some ++ [none]))

lemma link_left_wing_head (a : Option (Skeleton q k)) (b : Skeleton q k) (m : Marker)
    (hm : m = .left ∨ m = .boundary ∨ m = .full) :
    Link a (some (b.mark m)) ↔ Link a (some (b.mark .left)) := by
  cases a with
  | none => rcases hm with rfl | rfl | rfl <;> simp [Link, leftExternal]
  | some a => exact left_wing_head a b m hm

lemma link_right_wing_head (a : Skeleton q k) (b : Option (Skeleton q k)) :
    Link (some (a.mark .full)) b ↔ Link (some (a.mark .right)) b := by
  cases b with
  | none => simp [Link, rightExternal]
  | some b => exact right_wing_head a b

lemma link_cursor_right (a : Skeleton q k) (b : Option (Skeleton q k)) :
    Link (some (a.mark .boundary)) b ↔ Link (some (a.mark .idle)) b := by
  cases b with
  | none => simp [Link, rightExternal]
  | some b => exact cursor_right a b

lemma link_create_left (a : Option (Skeleton q k)) (b : Skeleton q k) (hb : b.first) :
    Link a (some (b.mark .boundary)) ↔ Link a (some (b.mark .idle)) := by
  cases a with
  | none => simp [Link, leftExternal, hb]
  | some a => exact create_left a b hb

lemma link_finish_right (a : Skeleton q k) (b : Option (Skeleton q k)) (ha : a.last) :
    Link (some (a.mark .boundary)) b ↔ Link (some (a.mark .full)) b := by
  cases b with
  | none => simp [Link, rightExternal, ha]
  | some b => exact finish_right a b ha

end Skeleton

section Chains
variable {α : Type*} {R : α → α → Prop}

lemma chain_change_head (s : List α) (a b : α) (h : ∀ c, R a c ↔ R b c) :
    List.IsChain R (a :: s) ↔ List.IsChain R (b :: s) := by
  cases s with
  | nil => simp
  | cons c s => simp only [List.isChain_cons_cons, h c]

lemma chain_change_last (p : List α) (a b : α) (h : ∀ c, R c a ↔ R c b) :
    List.IsChain R (p ++ [a]) ↔ List.IsChain R (p ++ [b]) := by
  induction p with
  | nil => simp
  | cons c p ih =>
    cases p with
    | nil => simpa only [List.cons_append, List.nil_append, List.isChain_pair] using h c
    | cons d p =>
      simp only [List.cons_append, List.isChain_cons_cons] at ih ⊢
      exact and_congr Iff.rfl ih

lemma chain_replace_one (p s : List α) (a b : α)
    (hl : ∀ c, R c a ↔ R c b) (hr : ∀ c, R a c ↔ R b c) :
    List.IsChain R (p ++ a :: s) ↔ List.IsChain R (p ++ b :: s) := by
  exact List.isChain_split.trans ((and_congr (chain_change_last p a b hl)
    (chain_change_head s a b hr)).trans List.isChain_split.symm)

lemma chain_replace_two (p s : List α) (a b a' b' : α)
    (hl : ∀ c, R c a ↔ R c a') (hr : ∀ c, R b c ↔ R b' c)
    (hm : R a b ↔ R a' b') :
    List.IsChain R (p ++ a :: b :: s) ↔ List.IsChain R (p ++ a' :: b' :: s) := by
  rw [List.isChain_append_cons_cons, List.isChain_append_cons_cons,
    chain_change_last p a a' hl, chain_change_head s b b' hr, hm]

end Chains

namespace Skeleton
variable {q k : ℕ}

lemma closed_replace_one (p s : List (Skeleton q k)) (a b : Skeleton q k)
    (ha : a.Admissible ↔ b.Admissible)
    (hl : ∀ c, Link c (some a) ↔ Link c (some b))
    (hr : ∀ c, Link (some a) c ↔ Link (some b) c) :
    Closed (p ++ a :: s) ↔ Closed (p ++ b :: s) := by
  have hn : (∀ c ∈ p ++ a :: s, c.Admissible) ↔
      (∀ c ∈ p ++ b :: s, c.Admissible) := by
    simp only [List.forall_mem_append, List.forall_mem_cons, ha]
  have hc := chain_replace_one (none :: p.map some) (s.map some ++ [none])
    (some a) (some b) hl hr
  exact and_congr hn (by simpa only [List.map_append, List.map_cons,
    List.append_assoc, List.cons_append] using hc)

lemma closed_replace_two (p s : List (Skeleton q k)) (a b a' b' : Skeleton q k)
    (ha : a.Admissible) (hb : b.Admissible)
    (ha' : a'.Admissible) (hb' : b'.Admissible)
    (hl : ∀ c, Link c (some a) ↔ Link c (some a'))
    (hr : ∀ c, Link (some b) c ↔ Link (some b') c)
    (hm : Pair a b ↔ Pair a' b') :
    Closed (p ++ a :: b :: s) ↔ Closed (p ++ a' :: b' :: s) := by
  have hn : (∀ c ∈ p ++ a :: b :: s, c.Admissible) ↔
      (∀ c ∈ p ++ a' :: b' :: s, c.Admissible) := by
    simp only [List.forall_mem_append, List.forall_mem_cons, ha, hb, ha', hb']
  have hc := chain_replace_two (none :: p.map some) (s.map some ++ [none])
    (some a) (some b) (some a') (some b') hl hr hm
  exact and_congr hn (by simpa only [List.map_append, List.map_cons,
    List.append_assoc, List.cons_append] using hc)

lemma admissible_idle (a : Skeleton q k) : (a.mark .idle).Admissible := by
  simp [Admissible]
lemma admissible_boundary (a : Skeleton q k) : (a.mark .boundary).Admissible := by
  simp [Admissible]
lemma admissible_full (a : Skeleton q k) : (a.mark .full).Admissible := by
  simp [Admissible]
lemma admissible_left (a : Skeleton q k) (h : ¬ a.last) : (a.mark .left).Admissible := by
  simp [Admissible, h]
lemma admissible_right (a : Skeleton q k) (h : ¬ a.first) : (a.mark .right).Admissible := by
  simp [Admissible, h]

lemma acquire_conditions {a b : Skeleton q k}
    (h : Pair (a.mark .left) (b.mark .boundary)) :
    Structural a b ∧ ¬ a.last := by
  rcases h with ⟨hs, he | hi⟩
  · simp [rightExternal] at he
  · exact ⟨hs, hi.2.2.2.2.2.2.2.2⟩

lemma full_conditions {a b : Skeleton q k}
    (h : Pair (a.mark .full) (b.mark .right)) : ¬ a.last ∧ ¬ b.first := by
  rcases h with ⟨_, he | hi⟩
  · simp [leftExternal] at he
  · exact ⟨hi.2.2.2.2.2.2.2.2, hi.2.2.2.2.2.2.2.1⟩

inductive Replacement : List (Skeleton q k) → List (Skeleton q k) → Prop
  | create (c : Skeleton q k) (hc : c.first) :
      Replacement [c.mark .idle] [c.mark .boundary]
  | acquire (a b : Skeleton q k) (h : Pair (a.mark .left) (b.mark .boundary)) :
      Replacement [a.mark .boundary, b.mark .idle] [a.mark .left, b.mark .boundary]
  | finish (c : Skeleton q k) (hc : c.last) :
      Replacement [c.mark .boundary] [c.mark .full]
  | sweep (a b : Skeleton q k) (h : Pair (a.mark .full) (b.mark .right)) :
      Replacement [a.mark .full, b.mark .right] [a.mark .left, b.mark .full]

theorem replacement_context {v w : List (Skeleton q k)} (h : Replacement v w)
    (p s : List (Skeleton q k)) : Closed (p ++ v ++ s) ↔ Closed (p ++ w ++ s) := by
  cases h with
  | create c hc =>
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply closed_replace_one
    · exact iff_of_true (admissible_idle c) (admissible_boundary c)
    · intro a; exact (link_create_left a c hc).symm
    · intro b; exact (link_cursor_right c b).symm
  | acquire a b h =>
    obtain ⟨hst, hlast⟩ := acquire_conditions h
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply closed_replace_two _ _ _ _ _ _ (admissible_boundary a) (admissible_idle b)
      (admissible_left a hlast) (admissible_boundary b)
    · intro c; exact link_left_wing_head c a _ (Or.inr (Or.inl rfl))
    · intro c; exact (link_cursor_right b c).symm
    · apply iff_of_true _ h
      simp [Pair, structural_mark_left, structural_mark_right, rightExternal,
        leftExternal, hst]
  | finish c hc =>
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply closed_replace_one
    · exact iff_of_true (admissible_boundary c) (admissible_full c)
    · intro a
      exact (link_left_wing_head a c _ (Or.inr (Or.inl rfl))).trans
        (link_left_wing_head a c _ (Or.inr (Or.inr rfl))).symm
    · intro b; exact link_finish_right c b hc
  | sweep a b h =>
    obtain ⟨ha, hb⟩ := full_conditions h
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply closed_replace_two _ _ _ _ _ _ (admissible_full a) (admissible_right b hb)
      (admissible_left a ha) (admissible_full b)
    · intro c; exact link_left_wing_head c a _ (Or.inr (Or.inr rfl))
    · intro c; exact (link_right_wing_head b c).symm
    · exact full_move_pair a b

def Step (v w : List (Skeleton q k)) : Prop :=
  ∃ p s a b, (Replacement a b ∨ Replacement b a) ∧ v = p ++ a ++ s ∧ w = p ++ b ++ s
abbrev Reach := Relation.ReflTransGen (Step (q := q) (k := k))

lemma closed_step_iff {v w : List (Skeleton q k)} (h : Step v w) : Closed v ↔ Closed w := by
  obtain ⟨p, s, a, b, h, rfl, rfl⟩ := h
  exact h.elim (fun h => replacement_context h p s) (fun h => (replacement_context h p s).symm)

theorem closed_reach {v w : List (Skeleton q k)} (h : Reach v w) (hv : Closed v) : Closed w := by
  induction h with
  | refl => exact hv
  | tail _ h ih => exact (closed_step_iff h).mp ih

lemma external_entrance {a b : Skeleton q k} (h : Pair a b)
    (he : a.rightExternal) (hb : b.marker ≠ .idle) : b.first := by
  rcases h.2 with hh | hh
  · exact (hh.2.resolve_left hb).2
  · exact (hh.1 he).elim

def InternalPair (a b : Skeleton q k) : Prop := Pair a b ∧ ¬ a.rightExternal

def IsHead (c : Skeleton q k) : Prop := c.marker = .boundary ∨ c.marker = .full

instance (c : Skeleton q k) : Decidable c.IsHead :=
  inferInstanceAs (Decidable (c.marker = .boundary ∨ c.marker = .full))

def RegionForm (w : List (Skeleton q k)) : Prop :=
  ∃ p h s, w = p ++ h :: s ∧ (∀ c ∈ p, c.marker = .left) ∧
    ((h.marker = .boundary ∧ s = []) ∨
      (h.marker = .full ∧ ∀ c ∈ s, c.marker = .right))

lemma internal_marker_rule {a b : Skeleton q k} (h : InternalPair a b) :
    (a.marker = .left ∧ (b.marker = .left ∨ b.marker = .boundary ∨ b.marker = .full)) ∨
    ((a.marker = .full ∨ a.marker = .right) ∧ b.marker = .right) := by
  obtain ⟨⟨_, he | hi⟩, hx⟩ := h
  · exact (hx he.1).elim
  · have hr := hi.2.2.1
    cases hm : a.marker <;> simp [rightExternal, hm] at hx <;>
      simp_all [acceptsRight]

lemma right_wing_constant (a : Skeleton q k) (w : List (Skeleton q k))
    (hc : (a :: w).IsChain InternalPair) (ha : a.marker = .right) :
    ∀ c ∈ a :: w, c.marker = .right := by
  induction w generalizing a with
  | nil => simpa using ha
  | cons b w ih =>
    obtain ⟨hab, hc⟩ := List.isChain_cons_cons.mp hc
    have hb : b.marker = .right := by
      have hr := internal_marker_rule hab
      simpa [ha] using hr
    intro c hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ha
    · exact ih b hc hb c hm

lemma form_of_chain (a : Skeleton q k) (w : List (Skeleton q k))
    (hc : (a :: w).IsChain InternalPair)
    (ha : a.marker = .left ∨ a.marker = .boundary ∨ a.marker = .full)
    (he : ∀ c ∈ (a :: w).getLast?, c.rightExternal) : RegionForm (a :: w) := by
  induction w generalizing a with
  | nil =>
    have he' : a.rightExternal := he a (by simp)
    rcases ha with ha | ha | ha
    · simp [rightExternal, ha] at he'
    · exact ⟨[], a, [], rfl, by simp, Or.inl ⟨ha, rfl⟩⟩
    · exact ⟨[], a, [], rfl, by simp, Or.inr ⟨ha, by simp⟩⟩
  | cons b w ih =>
    obtain ⟨hab, hc⟩ := List.isChain_cons_cons.mp hc
    have hr := internal_marker_rule hab
    rcases ha with ha | ha | ha
    · have hb : b.marker = .left ∨ b.marker = .boundary ∨ b.marker = .full := by
        simpa [ha] using hr
      obtain ⟨p, h, s, hw, hp, hh⟩ := ih b hc hb (by simpa using he)
      refine ⟨a :: p, h, s, ?_, ?_, hh⟩
      · simpa using congrArg (List.cons a) hw
      · intro c hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ha
        · exact hp c hm
    · simp [ha] at hr
    · have hb : b.marker = .right := by simpa [ha] using hr
      exact ⟨[], a, b :: w, rfl, by simp, Or.inr ⟨ha, right_wing_constant b w hc hb⟩⟩

theorem component_form (a : Skeleton q k) (w : List (Skeleton q k))
    (hc : (a :: w).IsChain InternalPair) (he : a.leftExternal)
    (hn : a.marker ≠ .idle) (hl : ∀ c ∈ (a :: w).getLast?, c.rightExternal) :
    RegionForm (a :: w) := by
  apply form_of_chain a w hc _ hl
  cases hm : a.marker <;> simp_all [leftExternal]

theorem region_unique_head {w : List (Skeleton q k)} (h : RegionForm w) :
    ∃ c, IsHead c ∧ w.filter (fun c => decide (IsHead c)) = [c] := by
  classical
  obtain ⟨p, c, s, rfl, hp, hs⟩ := h
  have hp' : p.filter (fun c => decide (IsHead c)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    simp [IsHead, hp a ha]
  rcases hs with ⟨hc, rfl⟩ | ⟨hc, hs⟩
  · exact ⟨c, Or.inl hc, by rw [List.filter_append, hp']; simp [IsHead, hc]⟩
  · have hs' : s.filter (fun c => decide (IsHead c)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro a ha
      simp [IsHead, hs a ha]
    exact ⟨c, Or.inr hc, by
      rw [List.filter_append, hp', List.filter_cons, hs']
      simp [IsHead, hc]⟩

def RightClosedComponent (w : List (Skeleton q k)) : Prop :=
  w ≠ [] ∧ w.IsChain InternalPair ∧ ∀ c ∈ w.getLast?, c.rightExternal

def LeftClosedComponent (w : List (Skeleton q k)) : Prop :=
  ∀ c ∈ w.head?, c.leftExternal

lemma decompose_pair_chain (a : Skeleton q k) (w : List (Skeleton q k))
    (hc : (a :: w).IsChain Pair)
    (he : ∀ c ∈ (a :: w).getLast?, c.rightExternal) :
    ∃ u us, (u :: us).flatten = a :: w ∧ u.head? = some a ∧
      RightClosedComponent u ∧
      ∀ v ∈ us, RightClosedComponent v ∧ LeftClosedComponent v := by
  classical
  induction w generalizing a with
  | nil => exact ⟨[a], [], rfl, rfl, by simpa [RightClosedComponent] using he, by simp⟩
  | cons b w ih =>
    obtain ⟨hab, hc⟩ := List.isChain_cons_cons.mp hc
    obtain ⟨u, us, hu, hhead, hur, hus⟩ := ih b hc (by simpa using he)
    by_cases ha : a.rightExternal
    · have hb : b.leftExternal := by
        rcases hab.2 with hh | hh
        · exact hh.2
        · exact (hh.1 ha).elim
      refine ⟨[a], u :: us, ?_, rfl, ?_, ?_⟩
      · simp [List.flatten_cons, hu]
      · simp [RightClosedComponent, ha]
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨hur, by simpa [LeftClosedComponent, hhead] using hb⟩
        · exact hus v hv
    · refine ⟨a :: u, us, ?_, rfl, ?_, hus⟩
      · simpa [List.flatten_cons] using congrArg (List.cons a) hu
      · refine ⟨by simp, hur.2.1.cons ?_, ?_⟩
        · simpa [hhead] using (show InternalPair a b from ⟨hab, ha⟩)
        · simpa [List.getLast?_cons_of_ne_nil hur.1] using hur.2.2

lemma closed_pair_chain {w : List (Skeleton q k)} (h : Closed w) : w.IsChain Pair := by
  have hc := h.2.tail.left_of_append
  simpa only [List.isChain_map, Link] using hc

lemma closed_right {w : List (Skeleton q k)} (h : Closed w) :
    ∀ c ∈ w.getLast?, c.rightExternal := by
  have hc := (List.isChain_append.mp h.2.tail).2.2
  intro c hc'
  have hh : some c ∈ (w.map some).getLast? := by simpa using hc'
  simpa [Link] using hc (some c) hh none (by simp)

lemma closed_left {w : List (Skeleton q k)} (h : Closed w) : LeftClosedComponent w := by
  cases w with
  | nil => simp [LeftClosedComponent]
  | cons a w =>
    have hh := (List.isChain_cons_cons.mp h.2).1
    simpa [LeftClosedComponent, Link] using hh

theorem closed_components {w : List (Skeleton q k)} (h : Closed w) :
    ∃ parts : List (List (Skeleton q k)), parts.flatten = w ∧
      ∀ u ∈ parts, RightClosedComponent u ∧ LeftClosedComponent u ∧
        ((∃ c, u = [c] ∧ c.marker = .idle) ∨ RegionForm u) := by
  cases w with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons a w =>
    obtain ⟨u, us, hu, hhead, hur, hus⟩ :=
      decompose_pair_chain a w (closed_pair_chain h) (closed_right h)
    have hul : LeftClosedComponent u := by
      simpa [LeftClosedComponent, hhead] using closed_left h
    refine ⟨u :: us, hu, ?_⟩
    intro v hv
    have hv' : RightClosedComponent v ∧ LeftClosedComponent v := by
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨hur, hul⟩
      · exact hus v hv
    refine ⟨hv'.1, hv'.2, ?_⟩
    rcases v with _ | ⟨b, v⟩
    · exact (hv'.1.1 rfl).elim
    · by_cases hb : b.marker = .idle
      · left
        cases v with
        | nil => exact ⟨b, rfl, hb⟩
        | cons c v =>
          have hn := (List.isChain_cons_cons.mp hv'.1.2.1).1.2
          exact (hn (Or.inl hb)).elim
      · right
        exact component_form b v hv'.1.2.1 (by simpa [LeftClosedComponent] using hv'.2)
          hb hv'.1.2.2

end Skeleton
end SourceBurnside.LocalSyntax

end

end OAI
