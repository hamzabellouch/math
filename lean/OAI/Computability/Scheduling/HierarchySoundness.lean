import OAI.Computability.Scheduling.HierarchyCompleteness

namespace OAI

section

namespace ThreeMachine.Structure
section Soundness
variable {J A : Type} [Fintype J] {r : J → J → Prop} {atoms : A → Set J}

structure FullBlock (r : J → J → Prop) (W : Set J) where
  length : ℕ
  time : J → ℕ
  bounds : ∀ x ∈ W, 1 ≤ time x ∧ time x ≤ length
  capacity : ∀ t, {x | x ∈ W ∧ time x = t}.ncard ≤ 3
  respects : ∀ x ∈ W, ∀ y ∈ W, r x y → time x < time y
  size : W.ncard = 3 * length

namespace FullBlock
variable {U V W : Set J}

def empty : FullBlock r (∅ : Set J) where
  length := 0
  time := fun _ => 0
  bounds := by simp
  capacity := by simp
  respects := by simp
  size := by simp

def triple (Z : Triple J) (hZ : ∀ x ∈ Z.val, ∀ y ∈ Z.val, ¬r x y) :
    FullBlock r (Z.val : Set J) where
  length := 1
  time := fun _ => 1
  bounds := by simp
  capacity := fun _ => (Set.ncard_le_ncard (fun _ hx => hx.1)).trans (by simpa using Z.property.le)
  respects := fun x hx y hy h => (hZ x hx y hy h).elim
  size := by simpa using Z.property

noncomputable def append (s : FullBlock r U) (t : FullBlock r V)
    (hd : Disjoint U V) (hback : ∀ x ∈ V, ∀ y ∈ U, ¬r x y) :
    FullBlock r (U ∪ V) := by
  classical
  let time : J → ℕ := fun x => if x ∈ U then s.time x else s.length + t.time x
  have htimeU (x : J) (hx : x ∈ U) : time x = s.time x := ite_eq_left hx
  have htimeV (x : J) (hx : x ∈ V) : time x = s.length + t.time x :=
    ite_eq_right (fun hu => Set.disjoint_left.mp hd hu hx)
  refine ⟨s.length + t.length, time, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · rw [htimeU x hx]
      have := s.bounds x hx
      omega
    · rw [htimeV x hx]
      have := t.bounds x hx
      omega
  · intro k
    by_cases hk : k ≤ s.length
    · have he : {x | x ∈ U ∪ V ∧ time x = k} = {x | x ∈ U ∧ s.time x = k} := by
        ext x
        constructor
        · rintro ⟨hx | hx, he⟩
          · exact ⟨hx, (htimeU x hx).symm.trans he⟩
          · rw [htimeV x hx] at he
            have := t.bounds x hx
            omega
        · rintro ⟨hx, he⟩
          exact ⟨Or.inl hx, (htimeU x hx).trans he⟩
      rw [he]
      exact s.capacity k
    · have he : {x | x ∈ U ∪ V ∧ time x = k} =
          {x | x ∈ V ∧ t.time x = k - s.length} := by
        ext x
        constructor
        · rintro ⟨hx | hx, he⟩
          · rw [htimeU x hx] at he
            have := s.bounds x hx
            omega
          · rw [htimeV x hx] at he
            exact ⟨hx, by omega⟩
        · rintro ⟨hx, he⟩
          refine ⟨Or.inr hx, ?_⟩
          rw [htimeV x hx, he]
          omega
      rw [he]
      exact t.capacity (k-s.length)
  · intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · simpa only [htimeU x hx, htimeU y hy] using s.respects x hx y hy hxy
    · rw [htimeU x hx, htimeV y hy]
      have := s.bounds x hx
      have := t.bounds y hy
      omega
    · exact (hback x hx y hy hxy).elim
    · simpa only [htimeV x hx, htimeV y hy, Nat.add_lt_add_iff_left] using
        t.respects x hx y hy hxy
  · rw [Set.ncard_union_eq hd, s.size, t.size, Nat.mul_add]

end FullBlock

namespace SplitVertex
variable {W : Set J} {u v : SplitVertex r atoms W}

omit [Fintype J] in
theorem gap_subset_right (_huv : u.left ∪ u.middle.val ⊆ v.left) :
    v.left \ (u.left ∪ u.middle.val) ⊆ u.right := by
  intro x hx
  rw [u.right_eq]
  exact ⟨v.left_subset hx.1, hx.2⟩

omit [Fintype J] in
theorem left_union_gap (huv : u.left ∪ u.middle.val ⊆ v.left) :
    (u.left ∪ u.middle.val) ∪ (v.left \ (u.left ∪ u.middle.val)) = v.left := by
  ext x
  constructor
  · intro hx
    exact hx.elim (fun h => huv h) (fun h => h.1)
  · intro hx
    by_cases hu : x ∈ u.left ∪ u.middle.val
    · exact Or.inl hu
    · exact Or.inr ⟨hx, hu⟩

noncomputable def add_middle (v : SplitVertex r atoms W) (s : FullBlock r v.left) :
    FullBlock r (v.left ∪ v.middle.val) :=
  s.append (FullBlock.triple v.middle v.antichain) v.left_middle v.no_middle_left

noncomputable def advance (s : FullBlock r u.left)
    (huv : u.left ∪ u.middle.val ⊆ v.left)
    (t : FullBlock r (v.left \ (u.left ∪ u.middle.val))) : FullBlock r v.left := by
  have hd : Disjoint (u.left ∪ u.middle.val) (v.left \ (u.left ∪ u.middle.val)) := by
    exact Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)
  have hback : ∀ x ∈ v.left \ (u.left ∪ u.middle.val),
      ∀ y ∈ u.left ∪ u.middle.val, ¬r x y := by
    intro x hx y hy
    have hxr := gap_subset_right huv hx
    exact hy.elim (u.no_right_left x hxr y) (u.no_right_middle x hxr y)
  exact left_union_gap huv ▸ (u.add_middle s).append t hd hback

noncomputable def finish (v : SplitVertex r atoms W)
    (s : FullBlock r v.left) (t : FullBlock r v.right) : FullBlock r W := by
  have hd : Disjoint (v.left ∪ v.middle.val) v.right := v.left_right.union_left v.middle_right
  have hback : ∀ x ∈ v.right, ∀ y ∈ v.left ∪ v.middle.val, ¬r x y := by
    intro x hx y hy
    exact hy.elim (v.no_right_left x hx y) (v.no_right_middle x hx y)
  have he : (v.left ∪ v.middle.val) ∪ v.right = W := by
    ext x
    simpa only [Set.mem_union, Finset.mem_coe, or_assoc] using (v.partition x).symm
  exact he ▸ (v.add_middle s).append t hd hback

theorem path_sound {P : Set J → Prop} (hP : ∀ U, P U → Nonempty (FullBlock r U))
    (h : Relation.ReflTransGen (Step P) u v) (hs : Nonempty (FullBlock r u.left)) :
    Nonempty (FullBlock r v.left) := by
  induction h with
  | refl => exact hs
  | tail _ ht ih =>
    obtain ⟨s⟩ := ih
    obtain ⟨t⟩ := hP _ ht.2
    exact ⟨advance s ht.1 t⟩

end SplitVertex

theorem AcceptedAt.sound {n : ℕ} {W : Set J} (h : AcceptedAt r atoms n W) :
    Nonempty (FullBlock r W) := by
  induction n generalizing W with
  | zero => exact h.2 ▸ ⟨FullBlock.empty⟩
  | succ n ih =>
    rcases h.2 with he | ⟨u, v, hu, hp, hv⟩
    · exact he ▸ ⟨FullBlock.empty⟩
    · obtain ⟨s⟩ := SplitVertex.path_sound (fun _ h => ih h) hp (ih hu)
      obtain ⟨t⟩ := ih hv
      exact ⟨v.finish s t⟩

end Soundness
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section AtomicFamily
variable {J : Type} [Fintype J]

inductive Atomic (J : Type) [Fintype J]
  | constant (value : Bool)
  | threshold (frame upper : Bool) (k : Fin (Fintype.card J + 2))
  | cone (frame : Bool) (kind : Fin 5) (Z : Triple J)
  deriving Fintype

namespace Atomic

def eval (r : J → J → Prop) (rank reverseRank : J → ℕ) : Atomic J → Set J
  | .constant b => if b then Set.univ else ∅
  | .threshold frame upper k =>
    let ρ := if frame then reverseRank else rank
    if upper then {x | ρ x ≤ k.val} else {x | k.val ≤ ρ x}
  | .cone frame kind Z =>
    let R := if frame then (fun x y => r y x) else r
    match kind.val with
    | 0 => Z.val
    | 1 => (Boundary.actual Z).pred R
    | 2 => (Boundary.actual Z).desc R
    | 3 => (Boundary.actual Z).weakPred R
    | _ => (Boundary.actual Z).weakDesc R

theorem eval_reversed (r : J → J → Prop) (rank reverseRank : J → ℕ)
    (a : Atomic J) :
    ∃ b : Atomic J, eval (fun x y => r y x) reverseRank rank a = eval r rank reverseRank b := by
  cases a with
  | constant b => exact ⟨.constant b, rfl⟩
  | threshold frame upper k =>
    refine ⟨.threshold (!frame) upper k, ?_⟩
    cases frame <;> rfl
  | cone frame kind Z =>
    refine ⟨.cone (!frame) kind Z, ?_⟩
    cases frame <;> rfl

theorem support (r : J → J → Prop) (rank reverseRank : J → ℕ)
    (hrank : ∀ x, rank x ≤ Fintype.card J) :
    AtomSupport (eval r rank reverseRank) r rank := by
  have htrue : Described (eval r rank reverseRank) Set.univ 1 :=
    Described.atom (atoms := eval r rank reverseRank) (.constant true)
  have hfalse : Described (eval r rank reverseRank) ∅ 1 :=
    Described.atom (atoms := eval r rank reverseRank) (.constant false)
  refine ⟨htrue, hfalse, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k < Fintype.card J + 2
    · exact Described.atom (atoms := eval r rank reverseRank) (.threshold false false ⟨k, hk⟩)
    · have he : RankTail rank k = ∅ := by
        ext x
        have := hrank x
        simp only [RankTail, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        omega
      exact he ▸ hfalse
  · intro B
    cases B with
    | left => exact hfalse
    | right => exact htrue
    | actual Z => exact Described.atom (atoms := eval r rank reverseRank) (.cone false 1 Z)
  · intro B
    cases B with
    | left => exact htrue
    | right => exact hfalse
    | actual Z => exact Described.atom (atoms := eval r rank reverseRank) (.cone false 2 Z)
  · intro B
    cases B with
    | left => exact hfalse
    | right => exact htrue
    | actual Z => exact Described.atom (atoms := eval r rank reverseRank) (.cone false 3 Z)
  · intro B
    cases B with
    | left => exact htrue
    | right => exact hfalse
    | actual Z => exact Described.atom (atoms := eval r rank reverseRank) (.cone false 4 Z)
  · intro Z
    exact Described.atom (atoms := eval r rank reverseRank) (.cone false 0 Z)

theorem support_reverse (r : J → J → Prop) (rank reverseRank : J → ℕ)
    (hrank : ∀ x, reverseRank x ≤ Fintype.card J) :
    AtomSupport (eval r rank reverseRank) (fun x y => r y x) reverseRank := by
  have transfer (S : Set J) (h : Described (eval (fun x y => r y x) reverseRank rank) S 1) :
      Described (eval r rank reverseRank) S 1 := by
    obtain ⟨f, hf, hk⟩ := h
    cases f with
    | leaf a b =>
      obtain ⟨a', ha'⟩ := eval_reversed r rank reverseRank a
      refine ⟨.leaf a' b, ?_, le_rfl⟩
      cases b <;> simpa only [Formula.eval, ha'] using hf
    | conj p q | disj p q =>
      have := p.leaves_pos
      have := q.leaves_pos
      simp only [Formula.leaves] at hk
      omega
  have h := support (fun x y => r y x) reverseRank rank hrank
  exact ⟨transfer _ h.truth, transfer _ h.falsity, fun k => transfer _ (h.rankTail k),
    fun B => transfer _ (h.pred B), fun B => transfer _ (h.desc B),
    fun B => transfer _ (h.weakPred B), fun B => transfer _ (h.weakDesc B),
    fun Z => transfer _ (h.triple Z)⟩

end Atomic
end AtomicFamily
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section Ranks
variable {J K : Type} [Fintype J] [LinearOrder K]

def rankOfKey (key : J → K) (x : J) : ℕ :=
  (Finset.univ.filter (fun y => key y < key x)).card + 1

theorem rankOfKey_strict {key : J → K} {x y : J} (h : key x < key y) :
    rankOfKey key x < rankOfKey key y := by
  have hsub : Finset.univ.filter (fun z => key z < key x) ⊂
      Finset.univ.filter (fun z => key z < key y) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.trans h⟩
    · intro he
      have hm : x ∈ Finset.univ.filter (fun z => key z < key y) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [← he] at hm
      exact lt_irrefl _ (Finset.mem_filter.mp hm).2
  have := Finset.card_lt_card hsub
  dsimp [rankOfKey]
  omega

theorem rankOfKey_bounds (key : J → K) (x : J) :
    1 ≤ rankOfKey key x ∧ rankOfKey key x ≤ Fintype.card J := by
  have hsub : Finset.univ.filter (fun y => key y < key x) ⊂ (Finset.univ : Finset J) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hm : x ∈ Finset.univ.filter (fun y => key y < key x) := by rw [he]; exact Finset.mem_univ _
    exact lt_irrefl _ (Finset.mem_filter.mp hm).2
  have := Finset.card_lt_card hsub
  simp only [Finset.card_univ] at this
  dsimp [rankOfKey]
  omega

theorem rankOfKey_injective {key : J → K} (hinj : Function.Injective key) :
    Function.Injective (rankOfKey key) := by
  intro x y he
  rcases lt_trichotomy (key x) (key y) with h | h | h
  · have := rankOfKey_strict h
    omega
  · exact hinj h
  · have := rankOfKey_strict h
    omega

end Ranks

section IndexedRanks
variable {n : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r]

def predecessorCount (x : Fin n) : ℕ := (Finset.univ.filter (fun y => r y x)).card

def jobKey (x : Fin n) : Lex (ℕ × Fin n) := toLex (predecessorCount r x, x)

def jobRank : Fin n → ℕ := rankOfKey (jobKey r)

def reverseJobRank (x : Fin n) : ℕ := n+1-jobRank r x

theorem jobKey_injective : Function.Injective (jobKey r) := by
  intro x y h
  exact congrArg (fun z : Lex (ℕ × Fin n) => (ofLex z).2) h

theorem jobRank_injective : Function.Injective (jobRank r) := rankOfKey_injective (jobKey_injective r)

theorem jobRank_bounds (x : Fin n) : 1 ≤ jobRank r x ∧ jobRank r x ≤ n := by
  simpa [jobRank] using rankOfKey_bounds (jobKey r) x

theorem jobRank_strict
    (hirr : ∀ x, ¬r x x) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    {x y : Fin n} (hxy : r x y) : jobRank r x < jobRank r y := by
  have hsub : Finset.univ.filter (fun z => r z x) ⊂ Finset.univ.filter (fun z => r z y) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htrans (Finset.mem_filter.mp hz).2 hxy⟩
    · intro he
      have hm : x ∈ Finset.univ.filter (fun z => r z y) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
      rw [← he] at hm
      exact hirr x (Finset.mem_filter.mp hm).2
  apply rankOfKey_strict
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (Finset.card_lt_card hsub))

theorem reverseJobRank_bounds (x : Fin n) : 1 ≤ reverseJobRank r x ∧ reverseJobRank r x ≤ n := by
  have := jobRank_bounds r x
  dsimp [reverseJobRank]
  omega

theorem reverseJobRank_injective : Function.Injective (reverseJobRank r) := by
  intro x y h
  apply jobRank_injective r
  have := jobRank_bounds r x
  have := jobRank_bounds r y
  dsimp [reverseJobRank] at h
  omega

theorem reverseJobRank_strict
    (hirr : ∀ x, ¬r x x) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    {x y : Fin n} (hxy : r y x) : reverseJobRank r x < reverseJobRank r y := by
  have := jobRank_strict r hirr htrans hxy
  have := jobRank_bounds r x
  dsimp [reverseJobRank]
  omega

end IndexedRanks
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section ScheduleLayouts
variable {J : Type} [Fintype J]

theorem exists_slot_embedding {T : ℕ} (time : J → ℕ)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T)
    (hcap : ∀ t, {x | time x = t}.ncard ≤ 3) :
    ∃ f : J → Fin (3*T), Function.Injective f ∧
      ∀ x, (f x).val / 3 + 1 = time x := by
  classical
  let slot : J → Fin T := fun x => ⟨time x - 1, by have := hbound x; omega⟩
  have hc (i : Fin T) : Fintype.card {x // slot x = i} ≤ 3 := by
    have he : {x | slot x = i} = {x | time x = i.val + 1} := by
      ext x
      simp only [Set.mem_ofPred_eq, Fin.ext_iff]
      change time x - 1 = i.val ↔ time x = i.val + 1
      have := hbound x
      omega
    rw [← Nat.card_eq_fintype_card]
    change {x | slot x = i}.ncard ≤ 3
    rw [he]
    exact hcap _
  let embed (i : Fin T) : {x // slot x = i} ↪ Fin 3 :=
    (Fintype.equivFin {x // slot x = i}).toEmbedding.trans
      (Fin.castLEEmb (by simpa using hc i))
  let code : (Σ i : Fin T, {x // slot x = i}) → Fin T × Fin 3 :=
    fun z => (z.1, embed z.1 z.2)
  have hcode : Function.Injective code := by
    rintro ⟨i, x⟩ ⟨j, y⟩ he
    obtain ⟨hij, hxy⟩ := Prod.mk.inj he
    cases hij
    have hxy' := (embed i).injective hxy
    change x = y at hxy'
    subst y
    rfl
  let f₀ : J → Fin T × Fin 3 := code ∘ (Equiv.sigmaFiberEquiv slot).symm
  have hf : Function.Injective f₀ := hcode.comp (Equiv.sigmaFiberEquiv slot).symm.injective
  let conv : Fin T × Fin 3 ≃ Fin (3*T) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm T 3))
  let f : J → Fin (3*T) := conv ∘ f₀
  refine ⟨f, conv.injective.comp hf, ?_⟩
  intro x
  have hidx : (embed (slot x) ⟨x, rfl⟩).val < 3 := (embed (slot x) ⟨x, rfl⟩).isLt
  change ((embed (slot x) ⟨x, rfl⟩).val + 3 * (slot x).val) / 3 + 1 = time x
  change ((embed (slot x) ⟨x, rfl⟩).val + 3 * (time x - 1)) / 3 + 1 = time x
  have := hbound x
  omega

theorem exists_layout_time {T : ℕ} (time : J → ℕ)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T)
    (hcap : ∀ t, {x | time x = t}.ncard ≤ 3)
    (hsize : Fintype.card J = 3 * T) :
    ∃ p : Layout J, ∀ x, p.time x = time x := by
  obtain ⟨f, hf, ht⟩ := exists_slot_embedding time hbound hcap
  let e : J ≃ Fin (3*T) := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by simpa using hsize⟩)
  let p : Layout J := e.trans (finCongr hsize.symm)
  exact ⟨p, ht⟩

theorem FullBlock.layout {r : J → J → Prop} (s : FullBlock r Set.univ) :
    ∃ p : Layout J, p.Full r := by
  have hsize : Fintype.card J = 3*s.length := by
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using s.size
  obtain ⟨p, hp⟩ := exists_layout_time s.time (fun x => s.bounds x (Set.mem_univ x))
    (fun t => by simpa only [Set.mem_univ, true_and] using s.capacity t) hsize
  refine ⟨p, ⟨s.length, hsize⟩, ?_⟩
  intro x y hxy
  simpa only [hp] using s.respects x (Set.mem_univ x) y (Set.mem_univ y) hxy

theorem accepted_iff_full_layout [DecidableEq J]
    (r : J → J → Prop) (rank reverseRank : J → ℕ)
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hrank : ∀ x, rank x ≤ Fintype.card J)
    (hrankR : ∀ x, reverseRank x ≤ Fintype.card J)
    (hinj : Function.Injective rank) (hinjR : Function.Injective reverseRank)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hstrictR : ∀ x y, r y x → reverseRank x < reverseRank y) :
    AcceptedAt r (Atomic.eval r rank reverseRank) (Fintype.card J) Set.univ ↔
      ∃ p : Layout J, p.Full r := by
  constructor
  · intro h
    obtain ⟨s⟩ := h.sound
    exact s.layout
  · rintro ⟨p, hp⟩
    have hA := Atomic.support r rank reverseRank hrank
    exact node_complete (Fintype.card J) r rank reverseRank p Set.univ
      (Fintype.card J+1) htrans hA (Atomic.support_reverse r rank reverseRank hrankR)
      (by omega) (fun x => by have := hrank x; omega)
      (fun x => by have := hrankR x; omega) hinj hinjR hstrict hstrictR
      (NodeData.root p hp hA) (by simp)

end ScheduleLayouts
end ThreeMachine.Structure

end

end OAI
