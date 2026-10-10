import OAI.Computability.Scheduling.NodeCertificates

namespace OAI

section

namespace ThreeMachine.Structure
section SplitGraph
variable {J A : Type}

def RelativeDescription (atoms : A → Set J) (W L : Set J) (k : ℕ) : Prop :=
  ∃ F, Described atoms F k ∧ L = W ∩ F

structure SplitVertex (r : J → J → Prop) (atoms : A → Set J) (W : Set J) where
  left : Set J
  middle : Triple J
  right : Set J
  partition : ∀ x, x ∈ W ↔ x ∈ left ∨ x ∈ middle.val ∨ x ∈ right
  left_middle : Disjoint left (middle.val : Set J)
  left_right : Disjoint left right
  middle_right : Disjoint (middle.val : Set J) right
  antichain : ∀ x ∈ middle.val, ∀ y ∈ middle.val, ¬r x y
  no_middle_left : ∀ x ∈ middle.val, ∀ y ∈ left, ¬r x y
  no_right_left : ∀ x ∈ right, ∀ y ∈ left, ¬r x y
  no_right_middle : ∀ x ∈ right, ∀ y ∈ middle.val, ¬r x y
  small_left : RelativeDescription atoms W left 10000
  small_right : RelativeDescription atoms W right 10000

namespace SplitVertex
variable {r : J → J → Prop} {atoms : A → Set J} {W : Set J}

@[ext] theorem ext {u v : SplitVertex r atoms W}
    (hl : u.left = v.left) (hm : u.middle = v.middle) (hr : u.right = v.right) : u = v := by
  cases u
  cases v
  cases hl
  cases hm
  cases hr
  rfl

def reverse (v : SplitVertex r atoms W) : SplitVertex (fun x y => r y x) atoms W :=
  { left := v.right, middle := v.middle, right := v.left
    partition := fun x => (v.partition x).trans (by tauto)
    left_middle := v.middle_right.symm, left_right := v.left_right.symm
    middle_right := v.left_middle.symm
    antichain := fun x hx y hy => v.antichain y hy x hx
    no_middle_left := fun x hx y hy => v.no_right_middle y hy x hx
    no_right_left := fun x hx y hy => v.no_right_left y hy x hx
    no_right_middle := fun x hx y hy => v.no_middle_left y hy x hx
    small_left := v.small_right, small_right := v.small_left }

@[simp] theorem reverse_reverse (v : SplitVertex r atoms W) : v.reverse.reverse = v := by
  apply ext <;> rfl

def AtTime (v : SplitVertex r atoms W) (time : J → ℕ) (s : ℕ) : Prop :=
  (∀ x, x ∈ v.left ↔ x ∈ W ∧ time x < s) ∧
  (∀ x, x ∈ v.middle.val ↔ x ∈ W ∧ time x = s) ∧
  (∀ x, x ∈ v.right ↔ x ∈ W ∧ s < time x)

theorem AtTime.unique {u v : SplitVertex r atoms W} {time : J → ℕ} {s : ℕ}
    (hu : u.AtTime time s) (hv : v.AtTime time s) : u = v := by
  apply ext
  · exact Set.ext (fun x => (hu.1 x).trans (hv.1 x).symm)
  · apply Subtype.ext
    exact Finset.ext (fun x => (hu.2.1 x).trans (hv.2.1 x).symm)
  · exact Set.ext (fun x => (hu.2.2 x).trans (hv.2.2 x).symm)

theorem left_subset (v : SplitVertex r atoms W) : v.left ⊆ W :=
  fun x hx => (v.partition x).mpr (Or.inl hx)

theorem middle_subset (v : SplitVertex r atoms W) : (v.middle.val : Set J) ⊆ W :=
  fun x hx => (v.partition x).mpr (Or.inr (Or.inl hx))

theorem right_subset (v : SplitVertex r atoms W) : v.right ⊆ W :=
  fun x hx => (v.partition x).mpr (Or.inr (Or.inr hx))

theorem right_eq (v : SplitVertex r atoms W) : v.right = W \ (v.left ∪ v.middle.val) := by
  ext x
  have hlm := Set.disjoint_left.mp v.left_middle
  have hlr := Set.disjoint_left.mp v.left_right
  have hmr := Set.disjoint_left.mp v.middle_right
  constructor
  · intro hx
    exact ⟨v.right_subset hx, fun h => h.elim (fun hl => hlr hl hx) (fun hm => hmr hm hx)⟩
  · rintro ⟨hx, hn⟩
    rcases (v.partition x).mp hx with hl | hm | hr
    · exact (hn (Or.inl hl)).elim
    · exact (hn (Or.inr hm)).elim
    · exact hr

theorem left_eq (v : SplitVertex r atoms W) : v.left = W \ (v.middle.val ∪ v.right) := by
  have := v.reverse.right_eq
  simpa only [reverse, Set.union_comm] using this

def Step (P : Set J → Prop) (u v : SplitVertex r atoms W) : Prop :=
  u.left ∪ u.middle.val ⊆ v.left ∧ P (v.left \ (u.left ∪ u.middle.val))

theorem gap_reverse {u v : SplitVertex r atoms W}
    (_huv : u.left ∪ u.middle.val ⊆ v.left) :
    u.right \ (v.middle.val ∪ v.right) = v.left \ (u.left ∪ u.middle.val) := by
  rw [u.right_eq, v.right_eq]
  have hvm := Set.disjoint_left.mp v.left_middle
  ext x
  constructor
  · rintro ⟨⟨hxW, hnu⟩, hnv⟩
    have hxv : x ∈ v.left := by
      by_contra hn
      exact hnv (Or.inr ⟨hxW, fun h => h.elim hn (fun hm => hnv (Or.inl hm))⟩)
    exact ⟨hxv, hnu⟩
  · rintro ⟨hxv, hnu⟩
    refine ⟨⟨v.left_subset hxv, hnu⟩, ?_⟩
    rintro (hm | ⟨_, hn⟩)
    · exact hvm hxv hm
    · exact hn (Or.inl hxv)

theorem step_reverse {P Q : Set J → Prop} {u v : SplitVertex r atoms W}
    (hPQ : ∀ X, P X → Q X) (h : Step P u v) : Step Q v.reverse u.reverse := by
  refine ⟨?_, ?_⟩
  · intro x hx
    change x ∈ u.right
    rw [u.right_eq]
    have hxW : x ∈ W := hx.elim (fun hx => v.right_subset hx) (fun hx => v.middle_subset hx)
    refine ⟨hxW, ?_⟩
    intro hu
    have hvl := h.1 hu
    exact hx.elim (fun hv => Set.disjoint_left.mp v.left_right hvl hv)
      (fun hv => Set.disjoint_left.mp v.left_middle hvl hv)
  · change Q (u.right \ (v.right ∪ v.middle.val))
    rw [Set.union_comm v.right, gap_reverse h.1]
    exact hPQ _ h.2

theorem step_mono {P Q : Set J → Prop} (hPQ : ∀ X, P X → Q X)
    {u v : SplitVertex r atoms W} (h : Step P u v) : Step Q u v :=
  ⟨h.1, hPQ _ h.2⟩

theorem path_reverse {P Q : Set J → Prop} (hPQ : ∀ X, P X → Q X)
    {u v : SplitVertex r atoms W} (h : Relation.ReflTransGen (Step P) u v) :
    Relation.ReflTransGen (Step Q) v.reverse u.reverse := by
  induction h with
  | refl => exact .refl
  | tail h hs ih => exact (Relation.ReflTransGen.single (step_reverse hPQ hs)).trans ih

end SplitVertex

def AcceptedAt (r : J → J → Prop) (atoms : A → Set J) : ℕ → Set J → Prop
  | 0, W => Described atoms W 10000 ∧ W = ∅
  | n+1, W => Described atoms W 10000 ∧ (W = ∅ ∨
      ∃ u v : SplitVertex r atoms W, AcceptedAt r atoms n u.left ∧
        Relation.ReflTransGen (SplitVertex.Step (AcceptedAt r atoms n)) u v ∧
        AcceptedAt r atoms n v.right)

namespace AcceptedAt
variable {r : J → J → Prop} {atoms : A → Set J}

theorem empty (h : Described atoms (∅ : Set J) 10000) (n : ℕ) :
    AcceptedAt r atoms n ∅ := by
  cases n with
  | zero => exact ⟨h, rfl⟩
  | succ n => exact ⟨h, Or.inl rfl⟩

theorem succ {n : ℕ} {W : Set J} (h : AcceptedAt r atoms n W) :
    AcceptedAt r atoms (n+1) W := by
  induction n generalizing W with
  | zero => exact ⟨h.1, Or.inl h.2⟩
  | succ n ih =>
    refine ⟨h.1, ?_⟩
    rcases h.2 with he | ⟨u, v, hu, hp, hv⟩
    · exact Or.inl he
    · exact Or.inr ⟨u, v, ih hu, Relation.ReflTransGen.mono (fun _ _ h => SplitVertex.step_mono (fun _ => ih) h) _ _ hp, ih hv⟩

theorem mono {n m : ℕ} {W : Set J} (h : AcceptedAt r atoms n W) (hnm : n ≤ m) :
    AcceptedAt r atoms m W := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction d with
  | zero => simpa using h
  | succ d ih => exact succ ih

theorem reverse {n : ℕ} {W : Set J} (h : AcceptedAt r atoms n W) :
    AcceptedAt (fun x y => r y x) atoms n W := by
  induction n generalizing W with
  | zero => exact h
  | succ n ih =>
    refine ⟨h.1, ?_⟩
    rcases h.2 with he | ⟨u, v, hu, hp, hv⟩
    · exact Or.inl he
    · exact Or.inr ⟨v.reverse, u.reverse, ih hv,
        SplitVertex.path_reverse (fun _ => ih) hp, ih hu⟩

end AcceptedAt
end SplitGraph
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section TemporalSplits
variable {J A : Type} [Fintype J] {r : J → J → Prop} {rank : J → ℕ}
    {atoms : A → Set J} {p q : Layout J} {W : Set J}

omit [Fintype J] in

theorem before_small (hA : AtomSupport atoms r rank) {H : Set J} {k : ℕ}
    (hH : Described atoms H k) (B : Boundary J) :
    Described atoms (B.before r H) (k+2) := by
  have h := (hA.pred B).union (hH.diff (hA.weakDesc B))
  simpa only [Boundary.before, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

noncomputable def SplitVertex.ofTime {a b s k : ℕ} {Z : Triple J} {F : Set J}
    (hp : p.Full r) (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hs : a < s ∧ s < b) (hZ : (Boundary.actual Z).At p.time (Fintype.card J / 3) s)
    (hF : Described atoms F k) (hk : k+1 ≤ 10000)
    (hZA : Described atoms (Z.val : Set J) 1)
    (hbefore : ∀ x ∈ W, x ∈ F ↔ p.time x < s) : SplitVertex r atoms W := by
  let L : Set J := {x | x ∈ W ∧ p.time x < s}
  let R : Set J := {x | x ∈ W ∧ s < p.time x}
  have hZm : ∀ x, x ∈ Z.val ↔ x ∈ W ∧ p.time x = s := by
    intro x
    rw [hZ.2.2 x]
    constructor
    · intro hx
      exact ⟨(hW x).mpr ⟨by omega, by omega⟩, hx⟩
    · exact And.right
  refine {
    left := L, middle := Z, right := R
    partition := ?_, left_middle := ?_, left_right := ?_, middle_right := ?_
    antichain := ?_, no_middle_left := ?_, no_right_left := ?_, no_right_middle := ?_
    small_left := ?_, small_right := ?_ }
  · intro x
    change x ∈ W ↔ (x ∈ W ∧ p.time x < s) ∨ x ∈ Z.val ∨ (x ∈ W ∧ s < p.time x)
    rw [hZm x]
    constructor
    · intro hx
      rcases lt_trichotomy (p.time x) s with h | h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (Or.inl ⟨hx, h⟩)
      · exact Or.inr (Or.inr ⟨hx, h⟩)
    · tauto
  · apply Set.disjoint_left.mpr
    intro x hx hm
    have := (hZm x).mp hm
    exact (ne_of_lt hx.2) this.2
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2.le) hy.2
  · apply Set.disjoint_left.mpr
    intro x hm hr
    have := (hZm x).mp hm
    exact (ne_of_gt hr.2) this.2
  · intro x hx y hy hxy
    have := (hZ.2.2 x).mp hx
    have := (hZ.2.2 y).mp hy
    have := hp.2 x y hxy
    omega
  · intro x hx y hy hxy
    have := (hZ.2.2 x).mp hx
    have := hy.2
    have := hp.2 x y hxy
    omega
  · intro x hx y hy hxy
    have := hx.2
    have := hy.2
    have := hp.2 x y hxy
    omega
  · intro x hx y hy hxy
    have := hx.2
    have := (hZ.2.2 y).mp hy
    have := hp.2 x y hxy
    omega
  · refine ⟨F, hF.mono (by omega), ?_⟩
    ext x
    change (x ∈ W ∧ p.time x < s) ↔ x ∈ W ∧ x ∈ F
    exact and_congr_right (fun hx => (hbefore x hx).symm)
  · refine ⟨Fᶜ \ (Z.val : Set J), (hF.compl.diff hZA).mono hk, ?_⟩
    ext x
    change (x ∈ W ∧ s < p.time x) ↔ x ∈ W ∧ x ∉ F ∧ x ∉ Z.val
    rw [hZ.2.2 x]
    constructor
    · rintro ⟨hx, ht⟩
      exact ⟨hx, fun h => (not_lt_of_ge ht.le) ((hbefore x hx).mp h), (ne_of_gt ht)⟩
    · rintro ⟨hx, hn, he⟩
      have ht : ¬p.time x < s := fun h => hn ((hbefore x hx).mpr h)
      exact ⟨hx, by omega⟩

theorem SplitVertex.ofTime_at {a b s k : ℕ} {Z : Triple J} {F : Set J}
    (hp : p.Full r) (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hs : a < s ∧ s < b) (hZ : (Boundary.actual Z).At p.time (Fintype.card J / 3) s)
    (hF : Described atoms F k) (hk : k+1 ≤ 10000)
    (hZA : Described atoms (Z.val : Set J) 1)
    (hbefore : ∀ x ∈ W, x ∈ F ↔ p.time x < s) :
    (ofTime hp hW hs hZ hF hk hZA hbefore).AtTime p.time s := by
  refine ⟨fun _ => Iff.rfl, ?_, fun _ => Iff.rfl⟩
  intro x
  change x ∈ Z.val ↔ x ∈ W ∧ p.time x = s
  rw [hZ.2.2 x]
  exact ⟨fun hx => ⟨(hW x).mpr ⟨by omega, by omega⟩, hx⟩, And.right⟩

theorem EdgeData.target_description [DecidableEq J]
    {a b v ap bp : ℕ} {B V A' B' : Boundary J}
    (D : EdgeData r rank atoms p W a b v ap bp B V A' B')
    (hA : AtomSupport atoms r rank) (hFinal : Described atoms D.finalCutoff 1) :
    ∃ F, Described atoms F 210 ∧ ∀ x ∈ W, x ∈ F ↔ p.time x < bp := by
  let F := V.before r D.finalCutoff ∩ B'.before r D.globalCutoff
  refine ⟨F, ?_, ?_⟩
  · exact (before_small hA hFinal V).inter (before_small hA D.cutoffSmall B')
  · intro x hx
    have hW : a < p.time x ∧ p.time x < b :=
      show x ∈ Window p.time a b from D.parent ▸ hx
    have hc := Boundary.separates_description D.full.2 (p.time_bounds D.full.1)
      D.centerAt D.centerSep (fun _ _ => Iff.rfl) x hx
    change x ∈ V.before r D.finalCutoff ∧ x ∈ B'.before r D.globalCutoff ↔ p.time x < bp
    constructor
    · rintro ⟨hv, hb⟩
      have hxE : x ∈ Window p.time a v := ⟨hW.1, hc.mp hv⟩
      exact (Boundary.separates_description D.full.2 (p.time_bounds D.full.1)
        D.targetAt D.targetSep (fun y hy => D.cutoffAgrees y (D.parent.symm ▸
          show y ∈ Window p.time a b from ⟨hy.1, hy.2.trans D.center_lt⟩)) x hxE).mp hb
    · intro ht
      have hxE : x ∈ Window p.time a v := ⟨hW.1, ht.trans_le D.target_le⟩
      refine ⟨hc.mpr hxE.2, ?_⟩
      exact (Boundary.separates_description D.full.2 (p.time_bounds D.full.1)
        D.targetAt D.targetSep (fun y hy => D.cutoffAgrees y (D.parent.symm ▸
          show y ∈ Window p.time a b from ⟨hy.1, hy.2.trans D.center_lt⟩)) x hxE).mpr ht

noncomputable def EdgeData.targetVertex [DecidableEq J]
    {a b v ap bp : ℕ} {B V A' B' : Boundary J}
    (D : EdgeData r rank atoms p W a b v ap bp B V A' B')
    (hA : AtomSupport atoms r rank) (hFinal : Described atoms D.finalCutoff 1) :
    SplitVertex r atoms W := by
  let Z := Classical.choose D.targetActual
  have hZ : B' = Boundary.actual Z := Classical.choose_spec D.targetActual
  let F := Classical.choose (D.target_description hA hFinal)
  have hF := Classical.choose_spec (D.target_description hA hFinal)
  exact SplitVertex.ofTime D.full (fun x => D.parent ▸ Iff.rfl)
    ⟨D.start_le.trans_lt D.strict, D.target_le.trans_lt D.center_lt⟩
    (hZ ▸ D.targetAt) hF.1 (by omega) (hA.triple Z) hF.2

theorem EdgeData.targetVertex_at [DecidableEq J]
    {a b v ap bp : ℕ} {B V A' B' : Boundary J}
    (D : EdgeData r rank atoms p W a b v ap bp B V A' B')
    (hA : AtomSupport atoms r rank) (hFinal : Described atoms D.finalCutoff 1) :
    (D.targetVertex hA hFinal).AtTime p.time bp := by
  unfold targetVertex
  exact SplitVertex.ofTime_at _ _ _ _ _ _ _ _

end TemporalSplits
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section PrefixPaths
variable {J A : Type} [Fintype J] {r : J → J → Prop} {rank : J → ℕ}
    {atoms : A → Set J} {p q : Layout J} {W : Set J} {P : Set J → Prop}

omit [Fintype J] in
theorem SplitVertex.AtTime.congr {u : SplitVertex r atoms W} {f g : J → ℕ} {s : ℕ}
    (h : u.AtTime f s) (hbefore : ∀ x, f x < s ↔ g x < s)
    (hafter : ∀ x, s < f x ↔ s < g x) : u.AtTime g s := by
  refine ⟨fun x => (h.1 x).trans (and_congr_right fun _ => hbefore x), ?_,
    fun x => (h.2.2 x).trans (and_congr_right fun _ => hafter x)⟩
  intro x
  rw [h.2.1 x]
  have hb := hbefore x
  have ha := hafter x
  apply and_congr_right
  intro _
  omega

def Reached (P : Set J → Prop) (r : J → J → Prop) (atoms : A → Set J)
    (W : Set J) (time : J → ℕ) (a s : ℕ) : Prop :=
  s = a ∨ ∃ u v : SplitVertex r atoms W, P u.left ∧
    Relation.ReflTransGen (SplitVertex.Step P) u v ∧ v.AtTime time s

theorem reached_start {a : ℕ} : Reached P r atoms W p.time a a := Or.inl rfl

theorem EdgeData.reached [DecidableEq J]
    {a b v ap bp : ℕ} {B V A' B' : Boundary J}
    (D : EdgeData r rank atoms p W a b v ap bp B V A' B')
    (hA : AtomSupport atoms r rank) (hFinal : Described atoms D.finalCutoff 1)
    (hprev : Reached P r atoms W p.time a ap)
    (hgap : P (Window p.time ap bp)) : Reached P r atoms W p.time a bp := by
  let w := D.targetVertex hA hFinal
  have hw : w.AtTime p.time bp := D.targetVertex_at hA hFinal
  have hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b := by intro x; rw [D.parent]
  right
  rcases hprev with he | ⟨u, z, hu, hp, hz⟩
  · have hleft : w.left = Window p.time ap bp := by
      ext x
      rw [hw.1 x, hW x]
      change ((a < p.time x ∧ p.time x < b) ∧ p.time x < bp) ↔
        ap < p.time x ∧ p.time x < bp
      have := D.target_le
      have := D.center_lt
      omega
    exact ⟨w, w, hleft.symm ▸ hgap, .refl, hw⟩
  · have hzW : z.left ∪ z.middle.val ⊆ w.left := by
      intro x hx
      rw [hw.1 x]
      rcases hx with hl | hm
      · have := (hz.1 x).mp hl
        exact ⟨this.1, this.2.trans D.strict⟩
      · have := (hz.2.1 x).mp hm
        exact ⟨this.1, this.2 ▸ D.strict⟩
    have hgapEq : w.left \ (z.left ∪ z.middle.val) = Window p.time ap bp := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_union, Finset.mem_coe, hw.1 x, hz.1 x, hz.2.1 x]
      rw [hW x]
      change (((a < p.time x ∧ p.time x < b) ∧ p.time x < bp) ∧
        ¬(((a < p.time x ∧ p.time x < b) ∧ p.time x < ap) ∨
          ((a < p.time x ∧ p.time x < b) ∧ p.time x = ap))) ↔
          ap < p.time x ∧ p.time x < bp
      have := D.start_le
      have := D.target_le
      have := D.center_lt
      omega
    exact ⟨u, w, hu, hp.tail ⟨hzW, hgapEq.symm ▸ hgap⟩, hw⟩

omit [Fintype J] in
theorem Reached.congr_time {f g : J → ℕ} {a s : ℕ}
    (h : Reached P r atoms W f a s) (hbefore : ∀ x, f x < s ↔ g x < s)
    (hafter : ∀ x, s < f x ↔ s < g x) : Reached P r atoms W g a s := by
  rcases h with he | ⟨u, v, hu, hp, hv⟩
  · exact Or.inl he
  · exact Or.inr ⟨u, v, hu, hp, hv.congr hbefore hafter⟩

end PrefixPaths
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section WalkPaths
variable {J A : Type} [Fintype J] {r : J → J → Prop} {rank : J → ℕ}
    {atoms : A → Set J} {p : Layout J} {W : Set J} {P : Set J → Prop}

omit [Fintype J] in
theorem NumericWalkData.reached {E : Finset J} {time priority : J → ℕ} {a lo count v : ℕ}
    (D : NumericWalkData E r time priority a lo count)
    (hpos : ∀ i, D.position i < v)
    (happly : ∀ (i : Fin (count+1)) (bp : ℕ), D.position i < bp → bp ≤ v →
      Separator E r time (PriorityCut priority (lo+i.val)) bp →
      Reached P r atoms W time a (D.position i) → Reached P r atoms W time a bp)
    (hfinal : Separator E r time (PriorityCut priority (lo+count)) v) :
    Reached P r atoms W time a v := by
  have hreach : ∀ i, Reached P r atoms W time a (D.position i) := by
    intro i
    induction i using Fin.induction with
    | zero => rw [D.first]; exact Or.inl rfl
    | succ i ih =>
      have hle := (D.steps i).1.le
      rcases hle.eq_or_lt with he | hl
      · exact he ▸ ih
      · exact happly i.castSucc (D.position i.succ) hl (hpos i.succ).le (D.steps i).2 ih
  exact happly (Fin.last count) v (hpos _) le_rfl hfinal (hreach _)

theorem separator_at {E : Finset J} {S : Set J} {s a v : ℕ}
    (hp : p.Full r) (hE : ∀ x, x ∈ E ↔ x ∈ Window p.time a v)
    (hs : 1 ≤ s ∧ s ≤ Fintype.card J / 3)
    (hsep : Separator E r p.time S s) :
    (Boundary.actual (p.triple hp.1 s hs.1 hs.2)).Separates r p.time
      (Window p.time a v) S s := by
  have heq : (↑E : Set J) = Window p.time a v := Set.ext hE
  rw [← heq]
  exact (Boundary.actual_separates (p.triple_at hp.1 s hs.1 hs.2)).mpr hsep

omit [Fintype J] in
theorem Boundary.Separates.mono_domain {time : J → ℕ} {U S : Set J} {B : Boundary J} {s : ℕ}
    (h : B.Separates r time W S s) (hUW : U ⊆ W) : B.Separates r time U S s :=
  ⟨fun x hx ht hn => h.1 x (hUW hx) ht hn, fun x hx ht hs => h.2 x (hUW hx) ht hs⟩

theorem Boundary.at_bounds {B : Boundary J} {s : ℕ}
    (h : B.At p.time (Fintype.card J / 3) s) : s ≤ Fintype.card J / 3 + 1 := by
  cases B with
  | left => dsimp [At] at h; omega
  | right => exact h.le
  | actual Z => exact h.2.1.trans (Nat.le_succ _)

theorem Boundary.actual_of_interior {B : Boundary J} {s : ℕ}
    (h : B.At p.time (Fintype.card J / 3) s)
    (hs : 1 ≤ s ∧ s ≤ Fintype.card J / 3) : ∃ Z, B = Boundary.actual Z := by
  cases B with
  | left => dsimp [At] at h; omega
  | right => dsimp [At] at h; omega
  | actual Z => exact ⟨Z, rfl⟩

end WalkPaths
end ThreeMachine.Structure

end

end OAI
