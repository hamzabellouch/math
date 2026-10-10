import OAI.Computability.Scheduling.EffectiveFamily

namespace OAI

section

namespace ThreeMachine.Algorithm
open Structure

structure Block (J : Type) where
  length : ℕ
  time : J → ℕ

namespace Block
variable {J : Type} [Fintype J] [DecidableEq J] {r : J → J → Prop}

def Valid (r : J → J → Prop) (W : Finset J) (s : Block J) : Prop :=
  ∃ b : FullBlock r (W : Set J), b.length = s.length ∧ b.time = s.time

def empty : Block J := ⟨0, fun _ => 0⟩
def triple : Block J := ⟨1, fun _ => 1⟩
def append (U : Finset J) (s t : Block J) : Block J :=
  ⟨s.length + t.length, fun x => if x ∈ U then s.time x else s.length + t.time x⟩

omit [Fintype J] [DecidableEq J] in
theorem valid_empty : (empty : Block J).Valid r ∅ := by
  let b : FullBlock r (↑(∅ : Finset J) : Set J) :=
    { length := 0
      time := fun _ => 0
      bounds := by simp
      capacity := by simp
      respects := by simp
      size := by simp }
  exact ⟨b, rfl, rfl⟩

omit [DecidableEq J] in
theorem valid_triple {Z : Finset J} (hc : Z.card = 3)
    (ha : ∀ x ∈ Z, ∀ y ∈ Z, ¬r x y) : (triple : Block J).Valid r Z :=
  ⟨FullBlock.triple ⟨Z,hc⟩ ha, rfl, rfl⟩

theorem valid_append {U V : Finset J} {s t : Block J}
    (hs : s.Valid r U) (ht : t.Valid r V) (hd : Disjoint U V)
    (hb : ∀ x ∈ V, ∀ y ∈ U, ¬r x y) : (append U s t).Valid r (U ∪ V) := by
  obtain ⟨s', hsl, hst⟩ := hs
  obtain ⟨t', htl, htt⟩ := ht
  have hd' : Disjoint (U : Set J) (V : Set J) := Finset.disjoint_coe.mpr hd
  let b := s'.append t' hd' hb
  let c : FullBlock r (↑(U ∪ V) : Set J) :=
    { length := b.length, time := b.time
      bounds := fun x hx => b.bounds x (by simpa using hx)
      capacity := fun k => by simpa using b.capacity k
      respects := fun x hx y hy hxy => b.respects x (by simpa using hx) y (by simpa using hy) hxy
      size := by simpa using b.size }
  refine ⟨c, ?_, ?_⟩
  · change s'.length + t'.length = s.length + t.length
    rw [hsl, htl]
  · funext x
    by_cases hx : x ∈ U <;> simp [c, b, FullBlock.append, append, hx, hsl, hst, htt]

omit [Fintype J] [DecidableEq J] in
theorem Valid.of_eq {U V : Finset J} {s : Block J} (h : s.Valid r U) (he : U = V) :
    s.Valid r V := he ▸ h

end Block

structure State (J : Type) where
  left : Finset J
  middle : Finset J
  right : Finset J
  deriving DecidableEq

namespace State
variable {J : Type} [Fintype J] [DecidableEq J] {r : J → J → Prop}

def candidate (W F Z : Finset J) : State J :=
  ⟨W ∩ F, Z, W \ ((W ∩ F) ∪ Z)⟩

def Compatible (r : J → J → Prop) (W : Finset J) (s : State J) : Prop :=
  (s.left ∪ s.middle) ∪ s.right = W ∧
  Disjoint s.left s.middle ∧ Disjoint s.left s.right ∧ Disjoint s.middle s.right ∧
  s.middle.card = 3 ∧
  (∀ x ∈ s.middle, ∀ y ∈ s.middle, ¬r x y) ∧
  (∀ x ∈ s.middle, ∀ y ∈ s.left, ¬r x y) ∧
  (∀ x ∈ s.right, ∀ y ∈ s.left, ¬r x y) ∧
  (∀ x ∈ s.right, ∀ y ∈ s.middle, ¬r x y)

instance [DecidableRel r] (W : Finset J) (s : State J) : Decidable (s.Compatible r W) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def upto (s : State J) : Finset J := s.left ∪ s.middle

def advance (u : State J) (s t : Block J) : Block J :=
  Block.append u.upto (Block.append u.left s Block.triple) t

def finish (u : State J) (s t : Block J) : Block J := advance u s t

omit [Fintype J] in
theorem Compatible.left_subset {W : Finset J} {u : State J} (h : u.Compatible r W) :
    u.left ⊆ W := by
  rw [← h.1]
  exact fun _ hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)

omit [Fintype J] in
theorem Compatible.right_subset {W : Finset J} {u : State J} (h : u.Compatible r W) :
    u.right ⊆ W := by
  rw [← h.1]
  exact Finset.subset_union_right

def toSplit {W : Finset J} {u : State J} (h : u.Compatible r W) :
    SplitVertex r (id : Set J → Set J) (W : Set J) where
  left := u.left
  middle := ⟨u.middle, h.2.2.2.2.1⟩
  right := u.right
  partition := by
    intro x
    change x ∈ W ↔ x ∈ u.left ∨ x ∈ u.middle ∨ x ∈ u.right
    rw [← h.1]
    simp only [Finset.mem_union, or_assoc]
  left_middle := Finset.disjoint_coe.mpr h.2.1
  left_right := Finset.disjoint_coe.mpr h.2.2.1
  middle_right := Finset.disjoint_coe.mpr h.2.2.2.1
  antichain := h.2.2.2.2.2.1
  no_middle_left := h.2.2.2.2.2.2.1
  no_right_left := h.2.2.2.2.2.2.2.1
  no_right_middle := h.2.2.2.2.2.2.2.2
  small_left := ⟨u.left, (Described.atom _).mono (by omega),
    (Set.inter_eq_right.mpr h.left_subset).symm⟩
  small_right := ⟨u.right, (Described.atom _).mono (by omega),
    (Set.inter_eq_right.mpr h.right_subset).symm⟩

theorem valid_advance {W : Finset J} {u v : State J} {s t : Block J}
    (hu : u.Compatible r W) (hv : v.Compatible r W) (hs : s.Valid r u.left)
    (hsub : u.upto ⊆ v.left) (ht : t.Valid r (v.left \ u.upto)) :
    (u.advance s t).Valid r v.left := by
  have hs' := Block.valid_append hs
    (Block.valid_triple hu.2.2.2.2.1 hu.2.2.2.2.2.1) hu.2.1 hu.2.2.2.2.2.2.1
  have hd : Disjoint u.upto (v.left \ u.upto) :=
    Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx)
  have hb : ∀ x ∈ v.left \ u.upto, ∀ y ∈ u.upto, ¬r x y := by
    intro x hx y hy
    have hxr : x ∈ u.right := by
      have hxW := hv.left_subset (Finset.mem_sdiff.mp hx).1
      rw [← hu.1] at hxW
      rcases Finset.mem_union.mp hxW with hp | hr
      · exact ((Finset.mem_sdiff.mp hx).2 hp).elim
      · exact hr
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hu.2.2.2.2.2.2.2.1 x hxr y hy
    · exact hu.2.2.2.2.2.2.2.2 x hxr y hy
  have he : u.upto ∪ (v.left \ u.upto) = v.left := Finset.union_sdiff_of_subset hsub
  exact (Block.valid_append hs' ht hd hb).of_eq he

theorem valid_finish {W : Finset J} {u : State J} {s t : Block J}
    (hu : u.Compatible r W) (hs : s.Valid r u.left) (ht : t.Valid r u.right) :
    (u.finish s t).Valid r W := by
  have hs' := Block.valid_append hs
    (Block.valid_triple hu.2.2.2.2.1 hu.2.2.2.2.2.1) hu.2.1 hu.2.2.2.2.2.2.1
  have hd : Disjoint u.upto u.right := Finset.disjoint_union_left.mpr ⟨hu.2.2.1,hu.2.2.2.1⟩
  have hb : ∀ x ∈ u.right, ∀ y ∈ u.upto, ¬r x y := by
    intro x hx y hy
    exact (Finset.mem_union.mp hy).elim
      (hu.2.2.2.2.2.2.2.1 x hx y) (hu.2.2.2.2.2.2.2.2 x hx y)
  exact (Block.valid_append hs' ht hd hb).of_eq hu.1

omit [Fintype J] in
theorem left_card_strict {W : Finset J} {u v : State J}
    (hu : u.Compatible r W) (hsub : u.upto ⊆ v.left) : u.left.card < v.left.card := by
  have he : u.upto.card = u.left.card + 3 := by
    rw [upto, Finset.card_union_of_disjoint hu.2.1, hu.2.2.2.2.1]
  have := Finset.card_le_card hsub
  omega

end State
end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm

def lookup {K V : Type} [DecidableEq K] : List (K × V) → K → Option V
  | [], _ => none
  | (a,b)::xs, k => if a = k then some b else lookup xs k

def Has {K V : Type} [DecidableEq K] (tab : List (K × V)) (k : K) : Prop :=
  ∃ v, lookup tab k = some v

theorem lookup_mem {K V : Type} [DecidableEq K] {tab : List (K × V)} {k : K} {v : V}
    (h : lookup tab k = some v) : (k,v) ∈ tab := by
  induction tab with
  | nil => simp [lookup] at h
  | cons a xs ih =>
    simp only [lookup] at h
    split_ifs at h with he
    · subst k
      have he' : a.2 = v := Option.some.inj h
      rw [← he']
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem has_iff_mem {K V : Type} [DecidableEq K] (tab : List (K × V)) (k : K) :
    Has tab k ↔ ∃ v, (k,v) ∈ tab := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v, lookup_mem hv⟩
  · induction tab with
    | nil => simp
    | cons a xs ih =>
      rintro ⟨v,hv⟩
      by_cases he : a.1 = k
      · exact ⟨a.2, by simp [lookup, he]⟩
      · rw [List.mem_cons] at hv
        rcases hv with hv | hv
        · exact (he (congrArg Prod.fst hv).symm).elim
        · obtain ⟨v',hv'⟩ := ih ⟨v,hv⟩
          exact ⟨v', by simp only [lookup, ite_eq_right he, hv']⟩

def firstResult {K V : Type} (f : K → Option V) : List K → Option V
  | [] => none
  | k::ks => match f k with
    | some v => some v
    | none => firstResult f ks

theorem firstResult_some {K V : Type} {f : K → Option V} {ks : List K} {v : V}
    (h : firstResult f ks = some v) : ∃ k ∈ ks, f k = some v := by
  induction ks with
  | nil => simp [firstResult] at h
  | cons k ks ih =>
    cases hf : f k with
    | none =>
      obtain ⟨k',hk',he⟩ := ih (by simpa only [firstResult, hf] using h)
      exact ⟨k', List.mem_cons_of_mem _ hk',he⟩
    | some u =>
      have he : u = v := Option.some.inj (by simpa only [firstResult, hf] using h)
      exact ⟨k,List.mem_cons_self,he ▸ hf⟩

theorem firstResult_has {K V : Type} (f : K → Option V) (ks : List K) :
    (∃ v, firstResult f ks = some v) ↔ ∃ k ∈ ks, ∃ v, f k = some v := by
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨k,hk,hv⟩ := firstResult_some hv
    exact ⟨k,hk,v,hv⟩
  · induction ks with
    | nil => simp
    | cons k ks ih =>
      rintro ⟨k',hk',v,hv⟩
      cases hf : f k with
      | some u => exact ⟨u, by simp [firstResult,hf]⟩
      | none =>
        have hk : k' ∈ ks := by
          rcases List.mem_cons.mp hk' with he | he
          · subst k'
            rw [hf] at hv
            contradiction
          · exact he
        obtain ⟨u,hu⟩ := ih ⟨k',hk,v,hv⟩
        exact ⟨u, by simpa only [firstResult,hf] using hu⟩

def tableOf {K V : Type} (ks : List K) (f : K → Option V) : List (K × V) :=
  ks.filterMap (fun k => (f k).map (fun v => (k,v)))

theorem mem_tableOf {K V : Type} (ks : List K) (f : K → Option V) (k : K) (v : V) :
    (k,v) ∈ tableOf ks f ↔ k ∈ ks ∧ f k = some v := by
  rw [tableOf,List.mem_filterMap]
  constructor
  · rintro ⟨a,ha,he⟩
    cases hf : f a with
    | none => simp [hf] at he
    | some b =>
      have hab : (a,b) = (k,v) := Option.some.inj (by simpa [hf] using he)
      cases hab
      exact ⟨ha,hf⟩
  · rintro ⟨hk,hv⟩
    exact ⟨k,hk, by simp [hv]⟩

theorem has_tableOf {K V : Type} [DecidableEq K] (ks : List K) (f : K → Option V) (k : K) :
    Has (tableOf ks f) k ↔ k ∈ ks ∧ ∃ v, f k = some v := by
  rw [has_iff_mem]
  simp only [mem_tableOf, exists_and_left]

inductive Walk {K : Type} (r : K → K → Prop) : ℕ → K → K → Prop
  | refl (a : K) : Walk r 0 a a
  | tail {n a b c} : Walk r n a b → r b c → Walk r (n+1) a c

namespace Walk
variable {K : Type} {r : K → K → Prop}

theorem of_path {a b : K} (h : Relation.ReflTransGen r a b) : ∃ n, Walk r n a b := by
  induction h with
  | refl => exact ⟨0,.refl _⟩
  | tail _ hs ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,.tail hn hs⟩

theorem rank_bound {ρ : K → ℕ} (hr : ∀ a b, r a b → ρ a < ρ b)
    {n a b} (h : Walk r n a b) : n + ρ a ≤ ρ b := by
  induction h with
  | refl => omega
  | tail _ hs ih => have := hr _ _ hs; omega

end Walk
end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm
open Structure
section DynamicProgram
variable {J : Type} [Fintype J] [DecidableEq J] (r : J → J → Prop) [DecidableRel r]

def states (family triples : List (Finset J)) (W : Finset J) : List (State J) :=
  (family.flatMap (fun F => triples.map (State.candidate W F))).filter (fun s => s.Compatible r W)

def tryAdvance (tab : List (Finset J × Block J)) (u : State J × Block J)
    (v : State J) : Option (Block J) :=
  if u.1.upto ⊆ v.left then (lookup tab (v.left \ u.1.upto)).map (u.1.advance u.2) else none

def expand (tab : List (Finset J × Block J)) (sts : List (State J))
    (marks : List (State J × Block J)) : List (State J × Block J) :=
  tableOf sts (fun v => match lookup marks v with
    | some s => some s
    | none => firstResult (fun u => tryAdvance tab u v) marks)

def markings (tab : List (Finset J × Block J)) (sts : List (State J)) :
    ℕ → List (State J × Block J)
  | 0 => tableOf sts (fun v => lookup tab v.left)
  | k+1 => expand tab sts (markings tab sts k)

def solve (tab : List (Finset J × Block J)) (family triples : List (Finset J))
    (W : Finset J) : Option (Block J) :=
  if W = ∅ then some Block.empty else
    firstResult (fun v => (lookup tab v.1.right).map (v.1.finish v.2))
      (markings tab (states r family triples W) (Fintype.card J))

def layers (family triples : List (Finset J)) : ℕ → List (Finset J × Block J)
  | 0 => [(∅, Block.empty)]
  | k+1 => tableOf family (solve r (layers family triples k) family triples)

def TableGood (tab : List (Finset J × Block J)) : Prop :=
  ∀ W s, (W,s) ∈ tab → s.Valid r W

def MarksGood (W : Finset J) (marks : List (State J × Block J)) : Prop :=
  ∀ u s, (u,s) ∈ marks → u.Compatible r W ∧ s.Valid r u.left

theorem states_compatible {family triples : List (Finset J)} {W : Finset J} {u : State J}
    (h : u ∈ states r family triples W) : u.Compatible r W := by
  exact of_decide_eq_true (List.mem_filter.mp h).2

omit [DecidableRel r] in
theorem markings_good {tab : List (Finset J × Block J)} {sts : List (State J)} {W : Finset J}
    (htab : TableGood r tab) (hsts : ∀ u ∈ sts, u.Compatible r W) (k : ℕ) :
    MarksGood r W (markings tab sts k) := by
  induction k with
  | zero =>
    intro u s h
    obtain ⟨hu, hs⟩ := (mem_tableOf sts _ u s).mp h
    exact ⟨hsts u hu, htab _ _ (lookup_mem hs)⟩
  | succ k ih =>
    intro v s h
    obtain ⟨hv, hs⟩ := (mem_tableOf sts _ v s).mp h
    refine ⟨hsts v hv, ?_⟩
    cases he : lookup (markings tab sts k) v with
    | some b =>
      have hb : b = s := Option.some.inj (by simpa only [he] using hs)
      exact hb ▸ (ih v b (lookup_mem he)).2
    | none =>
      obtain ⟨⟨u,b⟩, hu, hh⟩ := firstResult_some (by simpa only [he] using hs)
      simp only [tryAdvance] at hh
      split_ifs at hh with hsub
      · cases hg : lookup tab (v.left \ u.upto) with
        | none => simp [hg] at hh
        | some t =>
          have hes : u.advance b t = s := Option.some.inj (by simpa [hg] using hh)
          exact hes ▸ State.valid_advance (ih u b hu).1 (hsts v hv)
            (ih u b hu).2 hsub (htab _ _ (lookup_mem hg))

theorem solve_good {tab : List (Finset J × Block J)} (htab : TableGood r tab)
    (family triples : List (Finset J)) {W : Finset J} {s : Block J}
    (h : solve r tab family triples W = some s) : s.Valid r W := by
  simp only [solve] at h
  split_ifs at h with he
  · subst W
    have hs : Block.empty = s := Option.some.inj h
    exact hs ▸ Block.valid_empty
  · obtain ⟨⟨u,b⟩,hu,hs⟩ := firstResult_some h
    have hg := markings_good r htab (fun v hv => states_compatible r hv) (Fintype.card J) u b hu
    cases ht : lookup tab u.right with
    | none => simp [ht] at hs
    | some t =>
      have hes : u.finish b t = s := Option.some.inj (by simpa [ht] using hs)
      exact hes ▸ State.valid_finish hg.1 hg.2 (htab _ _ (lookup_mem ht))

theorem layers_good (family triples : List (Finset J)) (k : ℕ) :
    TableGood r (layers r family triples k) := by
  induction k with
  | zero =>
    intro W s h
    have he : (W,s) = (∅,Block.empty) := by simpa only [layers, List.mem_singleton] using h
    cases he
    exact Block.valid_empty
  | succ k ih =>
    intro W s h
    exact solve_good r ih family triples ((mem_tableOf family _ W s).mp h).2

omit [Fintype J] [DecidableRel r] in
theorem markings_stay {tab : List (Finset J × Block J)} {sts : List (State J)}
    {v : State J} (hv : v ∈ sts) {k : ℕ} (h : Has (markings tab sts k) v) :
    Has (markings tab sts (k+1)) v := by
  obtain ⟨s,hs⟩ := h
  apply (has_tableOf sts _ v).mpr
  exact ⟨hv,s,by simp only [hs]⟩

omit [Fintype J] [DecidableRel r] in
theorem markings_mono {tab : List (Finset J × Block J)} {sts : List (State J)}
    {v : State J} (hv : v ∈ sts) {k l : ℕ} (h : Has (markings tab sts k) v) (hkl : k ≤ l) :
    Has (markings tab sts l) v := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hkl
  clear hkl
  induction d with
  | zero => exact h
  | succ d ih => exact markings_stay hv ih

omit [Fintype J] [DecidableRel r] in
theorem markings_step {tab : List (Finset J × Block J)} {sts : List (State J)}
    {u v : State J} (hv : v ∈ sts) (hsub : u.upto ⊆ v.left)
    (hgap : Has tab (v.left \ u.upto)) {k : ℕ} (hu : Has (markings tab sts k) u) :
    Has (markings tab sts (k+1)) v := by
  apply (has_tableOf sts _ v).mpr
  refine ⟨hv, ?_⟩
  cases he : lookup (markings tab sts k) v with
  | some b => exact ⟨b,rfl⟩
  | none =>
    apply (firstResult_has _ _).mpr
    obtain ⟨s,hs⟩ := hu
    obtain ⟨t,ht⟩ := hgap
    exact ⟨(u,s),lookup_mem hs,u.advance s t,by simp [tryAdvance,hsub,ht]⟩

def Arc (tab : List (Finset J × Block J)) (sts : List (State J)) (u v : State J) : Prop :=
  u ∈ sts ∧ v ∈ sts ∧ u.upto ⊆ v.left ∧ Has tab (v.left \ u.upto)

omit [Fintype J] [DecidableRel r] in
theorem markings_walk {tab : List (Finset J × Block J)} {sts : List (State J)}
    {u v : State J} {k : ℕ} (hu : u ∈ sts) (hinit : Has tab u.left)
    (h : Walk (Arc tab sts) k u v) : Has (markings tab sts k) v := by
  induction h with
  | refl => exact (has_tableOf sts _ _).mpr ⟨hu,hinit⟩
  | tail _ hs ih => exact markings_step hs.2.1 hs.2.2.1 hs.2.2.2 (ih hu hinit)

theorem solve_complete_path {tab : List (Finset J × Block J)} {family triples : List (Finset J)}
    {W : Finset J} {u v : State J} (hu : u ∈ states r family triples W)
    (hv : v ∈ states r family triples W) (hinit : Has tab u.left) (hfinal : Has tab v.right)
    (hpath : Relation.ReflTransGen (Arc tab (states r family triples W)) u v) :
    ∃ s, solve r tab family triples W = some s := by
  by_cases he : W = ∅
  · exact ⟨Block.empty, by simp [solve,he]⟩
  obtain ⟨k,hk⟩ := Walk.of_path hpath
  have hbound : k ≤ Fintype.card J := by
    have hb := hk.rank_bound (ρ := fun s => s.left.card) (fun a b hh =>
      State.left_card_strict (states_compatible r hh.1) hh.2.2.1)
    have hc := Finset.card_le_univ v.left
    omega
  have hm := markings_mono hv (markings_walk hu hinit hk) hbound
  obtain ⟨s,hs⟩ := hm
  obtain ⟨t,ht⟩ := hfinal
  simp only [solve,ite_eq_right he]
  apply (firstResult_has _ _).mpr
  exact ⟨(v,s),lookup_mem hs,v.finish s t,by simp [ht]⟩

end DynamicProgram
end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm
open Structure
open scoped Classical
section EraseSplits
variable {J A : Type} [Fintype J] [DecidableEq J] {r : J → J → Prop}
    {atoms : A → Set J} {W : Set J}

omit [Fintype J] [DecidableEq J] in
@[ext] theorem State.ext {u v : State J} (hL : u.left = v.left)
    (hM : u.middle = v.middle) (hR : u.right = v.right) : u = v := by
  cases u
  cases v
  cases hL
  cases hM
  cases hR
  rfl

noncomputable def State.erase (v : SplitVertex r atoms W) : State J :=
  ⟨v.left.toFinset, v.middle.val, v.right.toFinset⟩

theorem State.erase_compatible (v : SplitVertex r atoms W) :
    (erase v).Compatible r W.toFinset := by
  classical
  refine ⟨?_, ?_, ?_, ?_, v.middle.property, ?_, ?_, ?_, ?_⟩
  · ext x
    simpa only [erase, Finset.mem_union, Set.mem_toFinset, or_assoc] using (v.partition x).symm
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp v.left_middle (Set.mem_toFinset.mp hx) hy
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp v.left_right (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy)
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp v.middle_right hx (Set.mem_toFinset.mp hy)
  · exact v.antichain
  · intro x hx y hy
    exact v.no_middle_left x hx y (Set.mem_toFinset.mp hy)
  · intro x hx y hy
    exact v.no_right_left x (Set.mem_toFinset.mp hx) y (Set.mem_toFinset.mp hy)
  · intro x hx y hy
    exact v.no_right_middle x (Set.mem_toFinset.mp hx) y hy

theorem State.erase_candidate (v : SplitVertex r atoms W) {F : Set J} (hF : v.left = W ∩ F) :
    candidate W.toFinset F.toFinset v.middle.val = erase v := by
  classical
  apply State.ext
  · ext x
    change x ∈ W.toFinset ∩ F.toFinset ↔ x ∈ v.left.toFinset
    simp only [Finset.mem_inter, Set.mem_toFinset,hF,Set.mem_inter_iff]
  · rfl
  · ext x
    change x ∈ W.toFinset \ ((W.toFinset ∩ F.toFinset) ∪ v.middle.val) ↔ x ∈ v.right.toFinset
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union, Set.mem_toFinset]
    rw [v.right_eq]
    simp only [Set.mem_sdiff, Set.mem_union, Finset.mem_coe, hF, Set.mem_inter_iff]

theorem State.erase_mem_states [DecidableRel r] (family triples : List (Finset J))
    (hfamily : ∀ F, Described atoms F 10000 → F.toFinset ∈ family)
    (htriples : ∀ Z : Triple J, Z.val ∈ triples) (v : SplitVertex r atoms W) :
    erase v ∈ states r family triples W.toFinset := by
  classical
  obtain ⟨F,hF,he⟩ := v.small_left
  apply List.mem_filter.mpr
  refine ⟨List.mem_flatMap.mpr ⟨F.toFinset,hfamily F hF,
    List.mem_map.mpr ⟨v.middle.val,htriples v.middle, erase_candidate v he⟩⟩, ?_⟩
  exact decide_eq_true (erase_compatible v)

theorem State.erase_inclusion {u v : SplitVertex r atoms W}
    (h : u.left ∪ u.middle.val ⊆ v.left) : (erase u).upto ⊆ (erase v).left := by
  classical
  intro x hx
  apply Set.mem_toFinset.mpr
  apply h
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Or.inl (Set.mem_toFinset.mp hx)
  · exact Or.inr hx

theorem State.erase_gap (u v : SplitVertex r atoms W) :
    (v.left \ (u.left ∪ u.middle.val)).toFinset = (erase v).left \ (erase u).upto := by
  classical
  ext x
  simp only [Set.mem_toFinset, Set.mem_sdiff, Set.mem_union, Finset.mem_coe,
    erase, upto, Finset.mem_sdiff, Finset.mem_union]

end EraseSplits

section Completeness
variable {J A : Type} [Fintype J] [DecidableEq J] (r : J → J → Prop) [DecidableRel r]
    (atoms : A → Set J) (family triples : List (Finset J))
    (hfamily : ∀ F, Described atoms F 10000 → F.toFinset ∈ family)
    (htriples : ∀ Z : Triple J, Z.val ∈ triples)

include hfamily htriples in
theorem layers_complete (k : ℕ) {W : Set J} (h : AcceptedAt r atoms k W) :
    Has (layers r family triples k) W.toFinset := by
  classical
  induction k generalizing W with
  | zero =>
    have he : W = ∅ := h.2
    subst W
    refine ⟨Block.empty, ?_⟩
    simp [layers, lookup]
  | succ k ih =>
    apply (has_tableOf family _ W.toFinset).mpr
    refine ⟨hfamily W h.1, ?_⟩
    rcases h.2 with he | ⟨u,v,hu,hp,hv⟩
    · subst W
      exact ⟨Block.empty,by simp [solve]⟩
    · have hstate (s : SplitVertex r atoms W) := State.erase_mem_states family triples hfamily htriples s
      apply solve_complete_path r (hstate u) (hstate v) (ih hu) (ih hv)
      clear hv
      induction hp with
      | refl => exact .refl
      | @tail v w _ hs ihp =>
        refine ihp.tail ⟨hstate v,hstate w,State.erase_inclusion hs.1,?_⟩
        rw [← State.erase_gap]
        simpa only [← Set.toFinite_toFinset] using ih hs.2

end Completeness
end ThreeMachine.Algorithm

end

end OAI
