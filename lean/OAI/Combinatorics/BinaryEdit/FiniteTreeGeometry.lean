import OAI.Combinatorics.BinaryEdit.FiniteTreeWords

namespace OAI

/-! Concrete tagged leaf states and subtree locality for the finite tree. -/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

/-- The finite leaf set, represented by ordered paths of exactly `k` edges. -/
abbrev Leaf (m k : ℕ) := Word (Fin m) k

/-- The manuscript's product of cyclic leaf coordinates. -/
abbrev State {m k : ℕ} (Q : Leaf m k → ℕ) := ∀ l, ZMod (Q l)

/-- A symbol retains both its leaf tag and its cyclic state. -/
abbrev Symbol {m k : ℕ} (Q : Leaf m k → ℕ) := Σ l, ZMod (Q l)

/-- Decode an actual leaf path. The fallback only totalizes this function on
paths of the wrong length; the root construction never evaluates that branch. -/
def leafDecoder {m k : ℕ} (Q : Leaf m k → ℕ) (base : Leaf m k)
    (p : List (Fin m)) (x : State Q) : Symbol Q :=
  if hp : p.length = k then ⟨⟨p, hp⟩, x ⟨p, hp⟩⟩ else ⟨base, x base⟩

@[simp] theorem leafDecoder_of_length {m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (p : List (Fin m)) (hp : p.length = k) (x : State Q) :
    leafDecoder Q base p x = ⟨⟨p, hp⟩, x ⟨p, hp⟩⟩ := by
  simp [leafDecoder, hp]

/-- At a valid leaf, equality is exactly equality of that leaf's state. -/
theorem leafDecoder_eq_iff {m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (p : List (Fin m)) (hp : p.length = k) (x y : State Q) :
    leafDecoder Q base p x = leafDecoder Q base p y ↔
      x ⟨p, hp⟩ = y ⟨p, hp⟩ := by
  simp [leafDecoder, hp]

/-- The recursive word depends only on the coordinates below its prefix,
even though ancestor shifts may offset all coordinates of the supplied state. -/
theorem nodeWord_state_congr {T m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (u : List (Fin m) → State Q)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x y : State Q) (hagree : ∀ l : Leaf m k, p <+: l.val → x l = y l) :
    nodeWord T (leafDecoder Q base) u h p x =
      nodeWord T (leafDecoder Q base) u h p y := by
  induction h generalizing p x y with
  | zero =>
      have hp : p.length = k := by simpa using hlen
      simp only [nodeWord, List.singleton_inj]
      apply (leafDecoder_eq_iff Q base p hp x y).2
      exact hagree ⟨p, hp⟩ (by rfl)
  | succ h ih =>
      simp only [nodeWord]
      apply List.flatMap_congr
      intro a ha
      apply List.flatMap_congr
      intro i hi
      apply ih
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro l hl
        have hp : p <+: l.val := (List.prefix_append p [i]).trans hl
        simp only [Pi.add_apply, hagree l hp]

/-- The list-path and function-path presentations of the same leaf set. -/
def leafEquiv (m k : ℕ) : Leaf m k ≃ (Fin k → Fin m) :=
  Equiv.vectorEquivFin (Fin m) k

/-- Pull back a function-indexed cyclic state to the list-path presentation.
This is just relabeling coordinates, used to connect the closed-form vectors
to the list recursion. -/
def pullState {m k : ℕ} (Q : (Fin k → Fin m) → ℕ)
    (x : ∀ l, ZMod (Q l)) : State (fun l => Q (leafEquiv m k l)) :=
  fun l => x (leafEquiv m k l)

@[simp] theorem pullState_add {m k : ℕ} (Q : (Fin k → Fin m) → ℕ)
    (x y : ∀ l, ZMod (Q l)) :
    pullState Q (x + y) = pullState Q x + pullState Q y := rfl

@[simp] theorem pullState_nsmul {m k : ℕ} (Q : (Fin k → Fin m) → ℕ)
    (n : ℕ) (x : ∀ l, ZMod (Q l)) :
    pullState Q (n • x) = n • pullState Q x := rfl

@[simp] theorem pullState_zsmul {m k : ℕ} (Q : (Fin k → Fin m) → ℕ)
    (n : ℤ) (x : ∀ l, ZMod (Q l)) :
    pullState Q (n • x) = n • pullState Q x := rfl

/-- A nonzero residue shift changes the tagged symbol at a leaf. -/
theorem leafDecoder_ne_of_not_dvd {m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (p : List (Fin m)) (hp : p.length = k)
    (x z : State Q) (hz : z ⟨p, hp⟩ = 1) (t : ℤ)
    (ht : ¬ (Q ⟨p, hp⟩ : ℤ) ∣ t) :
    leafDecoder Q base p (x + t • z) ≠ leafDecoder Q base p x := by
  intro he
  have he' := (leafDecoder_eq_iff Q base p hp (x + t • z) x).1 he
  have hcast : (t : ZMod (Q ⟨p, hp⟩)) = 0 := by
    simpa [hz, add_eq_left] using he'
  exact ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t _).1 hcast)

/-- Two different singleton words have unit one-sided deficit. -/
theorem singleton_deficit_of_ne {Γ : Type*} (a b : Γ) (hab : a ≠ b) :
    deficit 1 [a] [b] = 1 := by
  have hset : {n : ℕ | ∃ z : List Γ, z.Sublist [a] ∧ z.Sublist [b] ∧ z.length = n}
      = {0} := by
    ext n
    constructor
    · rintro ⟨z, hza, hzb, rfl⟩
      rcases List.sublist_singleton.1 hza with rfl | rfl
      · simp
      · have : a = b := by simpa using hzb
        exact (hab this).elim
    · intro hn
      have : n = 0 := by simpa using hn
      subst n
      exact ⟨[], by simp⟩
  unfold deficit lcs
  rw [hset]
  simp

/-- The base case of finite separation, with the actual canonical deficit. -/
theorem leaf_deficit_of_not_dvd {m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (p : List (Fin m)) (hp : p.length = k)
    (x z : State Q) (hz : z ⟨p, hp⟩ = 1) (t : ℤ)
    (ht : ¬ (Q ⟨p, hp⟩ : ℤ) ∣ t) :
    deficit 1 [leafDecoder Q base p x] [leafDecoder Q base p (x + t • z)] = 1 := by
  apply singleton_deficit_of_ne
  exact (leafDecoder_ne_of_not_dvd Q base p hp x z hz t ht).symm

/-- State shifts agreeing below one node produce exactly the same subtree
word, giving support locality for the closed-form vectors. -/
theorem nodeWord_shift_congr {T m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (u : List (Fin m) → State Q)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x z w : State Q) (hagree : ∀ l : Leaf m k, p <+: l.val → z l = w l) :
    nodeWord T (leafDecoder Q base) u h p (x + z) =
      nodeWord T (leafDecoder Q base) u h p (x + w) := by
  apply nodeWord_state_congr Q base u h p hlen
  intro l hl
  simp only [Pi.add_apply, hagree l hl]

/-- The relative input shift between source row `a` and target row `b` in a
child is `(b-a+tR)` times its distinguished vector. The two support hypotheses
are precisely the coordinate restrictions of the explicit subtree vectors. -/
theorem child_relative_shift {T m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (u : List (Fin m) → State Q)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x wp up wc : State Q) (R t : ℤ) (a b : ℕ)
    (hu : ∀ l : Leaf m k, p <+: l.val → up l = wc l)
    (hw : ∀ l : Leaf m k, p <+: l.val → wp l = R • wc l) :
    nodeWord T (leafDecoder Q base) u h p (x + t • wp + b • up) =
      nodeWord T (leafDecoder Q base) u h p
        (x + a • up + ((b : ℤ) - (a : ℤ) + t * R) • wc) := by
  apply nodeWord_state_congr Q base u h p hlen
  intro l hl
  simp only [Pi.add_apply, Pi.smul_apply, hu l hl, hw l hl]
  simp only [zsmul_eq_mul, nsmul_eq_mul, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast]
  ring

end TreeEdit.BinaryLower.FiniteTree

end

end OAI
