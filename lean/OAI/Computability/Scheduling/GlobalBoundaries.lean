import OAI.Computability.Scheduling.SeparatorWalk

namespace OAI

section

namespace ThreeMachine.Structure

def GlobalUpset {J : Type} (r : J → J → Prop) (A : Set J) : Prop :=
  ∀ ⦃x y⦄, r x y → x ∈ A → y ∈ A

def GlobalDownset {J : Type} (r : J → J → Prop) (A : Set J) : Prop :=
  ∀ ⦃x y⦄, r x y → y ∈ A → x ∈ A

theorem GlobalUpset.inter {J : Type} {r : J → J → Prop} {A B : Set J}
    (hA : GlobalUpset r A) (hB : GlobalUpset r B) : GlobalUpset r (A ∩ B) := by
  intro x y hxy hx
  exact ⟨hA hxy hx.1, hB hxy hx.2⟩

theorem GlobalUpset.union {J : Type} {r : J → J → Prop} {A B : Set J}
    (hA : GlobalUpset r A) (hB : GlobalUpset r B) : GlobalUpset r (A ∪ B) := by
  intro x y hxy hx
  exact hx.elim (fun h => Or.inl (hA hxy h)) (fun h => Or.inr (hB hxy h))

theorem GlobalDownset.compl {J : Type} {r : J → J → Prop} {A : Set J}
    (hA : GlobalDownset r A) : GlobalUpset r Aᶜ := by
  intro x y hxy hx hy
  exact hx (hA hxy hy)

structure GlobalList (J : Type) where
  indices : Finset ℕ
  entry : ℕ → Set J

namespace GlobalList
variable {J : Type}

def Qual (K : GlobalList J) : Set J := {x | ∃ i ∈ K.indices, x ∈ K.entry i}

def Upsets (K : GlobalList J) (r : J → J → Prop) : Prop :=
  ∀ i ∈ K.indices, GlobalUpset r (K.entry i)

noncomputable def memberships (K : GlobalList J) (x : J) : Finset ℕ := by
  classical
  exact K.indices.filter (fun i => x ∈ K.entry i)

noncomputable def lastIndex (K : GlobalList J) (x : J) : ℕ :=
  (K.memberships x).sup id

def KeyLT (K : GlobalList J) (rank : J → ℕ) (x y : J) : Prop :=
  K.lastIndex x < K.lastIndex y ∨
    K.lastIndex x = K.lastIndex y ∧ rank x < rank y

@[simp] theorem mem_memberships (K : GlobalList J) (x : J) (i : ℕ) :
    i ∈ K.memberships x ↔ i ∈ K.indices ∧ x ∈ K.entry i := by
  classical
  simp [memberships]

theorem le_lastIndex {K : GlobalList J} {x : J} {i : ℕ}
    (hi : i ∈ K.indices) (hx : x ∈ K.entry i) : i ≤ K.lastIndex x := by
  exact Finset.le_sup (f := id) ((mem_memberships K x i).mpr ⟨hi, hx⟩)

theorem lastIndex_mem {K : GlobalList J} {x : J} (hx : x ∈ K.Qual) :
    K.lastIndex x ∈ K.indices ∧ x ∈ K.entry (K.lastIndex x) := by
  obtain ⟨i, hi, hxi⟩ := hx
  have hne : (K.memberships x).Nonempty := ⟨i, (mem_memberships K x i).mpr ⟨hi, hxi⟩⟩
  have := Finset.sup_mem_of_nonempty (f := id) hne
  obtain ⟨j, hj, e⟩ := this
  change j = K.lastIndex x at e
  apply (mem_memberships K x (K.lastIndex x)).mp
  rw [← e]
  exact hj

theorem qual_upset {K : GlobalList J} {r : J → J → Prop}
    (hK : K.Upsets r) : GlobalUpset r K.Qual := by
  rintro x y hxy ⟨i, hi, hx⟩
  exact ⟨i, hi, hK i hi hxy hx⟩

theorem key_extends {K : GlobalList J} {r : J → J → Prop} {rank : J → ℕ}
    (hK : K.Upsets r) (hrank : ∀ x y, r x y → rank x < rank y)
    {x y : J} (hx : x ∈ K.Qual) (hxy : r x y) : K.KeyLT rank x y := by
  obtain ⟨hi, hxlast⟩ := lastIndex_mem hx
  have hle : K.lastIndex x ≤ K.lastIndex y := le_lastIndex hi (hK _ hi hxy hxlast)
  rcases hle.lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hrank x y hxy⟩

noncomputable def carry (K : GlobalList J) (rank : J → ℕ) (d r : ℕ) : GlobalList J := by
  classical
  exact ⟨K.indices.filter (d ≤ ·), fun i =>
    if i = d then K.entry i ∩ {x | r ≤ rank x} else K.entry i⟩

theorem carry_membership (K : GlobalList J) (rank : J → ℕ) (d r i : ℕ) (x : J) :
    i ∈ (K.carry rank d r).memberships x ↔
      i ∈ K.indices ∧ d ≤ i ∧ x ∈ K.entry i ∧ (i = d → r ≤ rank x) := by
  classical
  rw [mem_memberships]
  change (i ∈ K.indices.filter (d ≤ ·) ∧
    x ∈ (if i = d then K.entry i ∩ {x | r ≤ rank x} else K.entry i)) ↔ _
  rw [Finset.mem_filter]
  by_cases hi : i = d <;> simp [hi, and_assoc]

theorem carry_selection (K : GlobalList J) (rank : J → ℕ) (d r : ℕ) (x : J) :
    x ∈ (K.carry rank d r).Qual ↔ x ∈ K.Qual ∧
      (d < K.lastIndex x ∨ K.lastIndex x = d ∧ r ≤ rank x) := by
  constructor
  · rintro ⟨i, hi, hx⟩
    have hc := (carry_membership K rank d r i x).mp
      ((mem_memberships _ _ _).mpr ⟨hi, hx⟩)
    refine ⟨⟨i, hc.1, hc.2.2.1⟩, ?_⟩
    have hle := le_lastIndex hc.1 hc.2.2.1
    by_cases h : d < K.lastIndex x
    · exact Or.inl h
    · have hid : i = d := by omega
      exact Or.inr ⟨by omega, hc.2.2.2 hid⟩
  · rintro ⟨hq, hmax⟩
    obtain ⟨hi, hx⟩ := lastIndex_mem hq
    refine ⟨K.lastIndex x, ?_⟩
    apply (mem_memberships _ _ _).mp
    apply (carry_membership K rank d r _ x).mpr
    refine ⟨hi, ?_, hx, ?_⟩
    · rcases hmax with h | ⟨h, _⟩ <;> omega
    · intro e
      rcases hmax with h | ⟨_, hr⟩
      · omega
      · exact hr

theorem carry_lastIndex {K : GlobalList J} {rank : J → ℕ} {d r : ℕ} {x : J}
    (hx : x ∈ (K.carry rank d r).Qual) :
    (K.carry rank d r).lastIndex x = K.lastIndex x := by
  have hsel := (carry_selection K rank d r x).mp hx
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    have hm := (carry_membership K rank d r i x).mp hi
    exact le_lastIndex hm.1 hm.2.2.1
  · obtain ⟨hi, hxi⟩ := lastIndex_mem hsel.1
    apply Finset.le_sup (f := id) (b := K.lastIndex x)
    apply (carry_membership K rank d r (K.lastIndex x) x).mpr
    refine ⟨hi, ?_, hxi, ?_⟩
    · rcases hsel.2 with h | ⟨h, _⟩ <;> omega
    · intro e
      rcases hsel.2 with h | ⟨_, hr⟩
      · omega
      · exact hr

theorem carry_key {K : GlobalList J} {rank : J → ℕ} {d r : ℕ} {x y : J}
    (hx : x ∈ (K.carry rank d r).Qual) (hy : y ∈ (K.carry rank d r).Qual) :
    (K.carry rank d r).KeyLT rank x y ↔ K.KeyLT rank x y := by
  simp only [KeyLT, carry_lastIndex hx, carry_lastIndex hy]

theorem carry_upsets {K : GlobalList J} {rank : J → ℕ} {d t : ℕ}
    {r : J → J → Prop} (hK : K.Upsets r)
    (hrank : ∀ x y, r x y → rank x < rank y) : (K.carry rank d t).Upsets r := by
  classical
  intro i hi x y hxy hx
  have hi' : i ∈ K.indices ∧ d ≤ i := by simpa [carry] using hi
  by_cases hid : i = d
  · have hx' : x ∈ K.entry i ∧ t ≤ rank x := by simpa [carry, hid] using hx
    have hrankxy := hrank x y hxy
    have hy : y ∈ K.entry i := hK i hi'.1 hxy hx'.1
    simpa [carry, hid] using And.intro hy (show t ≤ rank y by omega)
  · have hx' : x ∈ K.entry i := by simpa [carry, hid] using hx
    simpa [carry, hid] using hK i hi'.1 hxy hx'

noncomputable def prune (K : GlobalList J) (W : Set J) : GlobalList J := by
  classical
  exact ⟨K.indices.filter (fun i => (K.entry i ∩ W).Nonempty), K.entry⟩

theorem prune_membership (K : GlobalList J) (W : Set J) (i : ℕ) (x : J) :
    i ∈ (K.prune W).memberships x ↔
      i ∈ K.indices ∧ (K.entry i ∩ W).Nonempty ∧ x ∈ K.entry i := by
  classical
  rw [mem_memberships]
  change (i ∈ K.indices.filter (fun j => (K.entry j ∩ W).Nonempty) ∧
    x ∈ K.entry i) ↔ _
  rw [Finset.mem_filter]
  exact and_assoc

theorem prune_qual_subset (K : GlobalList J) (W : Set J) : (K.prune W).Qual ⊆ K.Qual := by
  rintro x ⟨i, hi, hx⟩
  have hm := (prune_membership K W i x).mp ((mem_memberships _ _ _).mpr ⟨hi, hx⟩)
  exact ⟨i, hm.1, hm.2.2⟩

theorem prune_qual (K : GlobalList J) {W : Set J} {x : J} (hx : x ∈ W) :
    x ∈ (K.prune W).Qual ↔ x ∈ K.Qual := by
  refine ⟨fun h => prune_qual_subset K W h, ?_⟩
  rintro ⟨i, hi, hxi⟩
  refine ⟨i, ?_⟩
  apply (mem_memberships _ _ _).mp
  exact (prune_membership K W i x).mpr ⟨hi, ⟨x, hxi, hx⟩, hxi⟩

theorem prune_lastIndex_le (K : GlobalList J) (W : Set J) (x : J) :
    (K.prune W).lastIndex x ≤ K.lastIndex x := by
  apply Finset.sup_le
  intro i hi
  have hm := (prune_membership K W i x).mp hi
  exact le_lastIndex hm.1 hm.2.2

theorem prune_lastIndex (K : GlobalList J) {W : Set J} {x : J} (hx : x ∈ W) :
    (K.prune W).lastIndex x = K.lastIndex x := by
  apply le_antisymm (prune_lastIndex_le K W x)
  apply Finset.sup_le
  intro i hi
  have hm := (mem_memberships K x i).mp hi
  apply Finset.le_sup (f := id)
  exact (prune_membership K W i x).mpr ⟨hm.1, ⟨x, hm.2, hx⟩, hm.2⟩

theorem prune_key {K : GlobalList J} {W : Set J} {rank : J → ℕ} {x y : J}
    (hx : x ∈ W) (hkey : (K.prune W).KeyLT rank x y) : K.KeyLT rank x y := by
  have heq := prune_lastIndex K hx
  have hle := prune_lastIndex_le K W y
  rcases hkey with h | ⟨h, hr⟩
  · exact Or.inl (by omega)
  · by_cases hlt : K.lastIndex x < K.lastIndex y
    · exact Or.inl hlt
    · exact Or.inr ⟨by omega, hr⟩

theorem prune_upsets {K : GlobalList J} {W : Set J} {r : J → J → Prop}
    (hK : K.Upsets r) : (K.prune W).Upsets r := by
  classical
  intro i hi
  have hi' : i ∈ K.indices ∧ (K.entry i ∩ W).Nonempty := by simpa [prune] using hi
  exact hK i hi'.1

end GlobalList
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section IntervalNormalization
variable {J : Type} [Fintype J]

def Layout.FixedOutside (p q : Layout J) (W : Set J) : Prop :=
  ∀ x, x ∉ W → q x = p x

theorem Layout.FixedOutside.refl (p : Layout J) (W : Set J) : p.FixedOutside p W :=
  fun _ _ => rfl

theorem Layout.FixedOutside.trans {p q u : Layout J} {W : Set J}
    (hpq : p.FixedOutside q W) (hqu : q.FixedOutside u W) : p.FixedOutside u W :=
  fun x hx => (hqu x hx).trans (hpq x hx)

theorem Layout.FixedOutside.mono {p q : Layout J} {W U : Set J}
    (h : p.FixedOutside q W) (hWU : W ⊆ U) : p.FixedOutside q U :=
  fun x hx => h x (fun hW => hx (hWU hW))

theorem Layout.FixedOutside.time {p q : Layout J} {W : Set J}
    (h : p.FixedOutside q W) {x : J} (hx : x ∉ W) : q.time x = p.time x := by
  simp [Layout.time, h x hx]

theorem Layout.FixedOutside.symm_position {p q : Layout J} {W : Set J}
    (h : p.FixedOutside q W) (i : Fin (Fintype.card J)) (hi : p.symm i ∉ W) :
    q.symm i = p.symm i := by
  apply q.injective
  rw [q.apply_symm_apply, h _ hi, p.apply_symm_apply]

theorem Layout.FixedOutside.position_mem {p q : Layout J} {W : Set J}
    (h : p.FixedOutside q W) {x : J} (hx : x ∈ W) : p.symm (q x) ∈ W := by
  by_contra hn
  have he : q (p.symm (q x)) = q x := by rw [h _ hn, p.apply_symm_apply]
  apply hn
  rw [q.injective he]
  exact hx

theorem Layout.FixedOutside.time_range {p q : Layout J} {W : Set J} {a b : ℕ}
    (h : p.FixedOutside q W) (hW : ∀ x ∈ W, a < p.time x ∧ p.time x < b)
    {x : J} (hx : x ∈ W) : a < q.time x ∧ q.time x < b := by
  have hr := hW _ (h.position_mem hx)
  simpa [Layout.time] using hr

theorem reorder_respects {p q : Layout J} {W : Set J} {a b : ℕ}
    {r : J → J → Prop} (hp : p.Respects r) (hfix : p.FixedOutside q W)
    (hW : ∀ x, x ∈ W ↔ a < p.time x ∧ p.time x < b)
    (hq : ∀ x ∈ W, ∀ y ∈ W, r x y → q.time x < q.time y) : q.Respects r := by
  intro x y hxy
  have ht := hp x y hxy
  by_cases hx : x ∈ W
  · by_cases hy : y ∈ W
    · exact hq x hx y hy hxy
    · have hxt := hfix.time_range (fun z hz => (hW z).mp hz) hx
      have hxp := (hW x).mp hx
      have hyp : ¬(a < p.time y ∧ p.time y < b) := fun h => hy ((hW y).mpr h)
      rw [hfix.time hy]
      omega
  · rw [hfix.time hx]
    by_cases hy : y ∈ W
    · have hyt := hfix.time_range (fun z hz => (hW z).mp hz) hy
      have hyp := (hW y).mp hy
      have hxp : ¬(a < p.time x ∧ p.time x < b) := fun h => hx ((hW x).mpr h)
      omega
    · rw [hfix.time hy]
      exact ht

def Layout.NormalizedOn (p : Layout J) (W : Set J)
    (r : J → J → Prop) (priority : J → ℕ) : Prop :=
  p.Respects r ∧ ∀ q : Layout J, q.Respects r → p.FixedOutside q W →
    p.signature priority ≤ q.signature priority

theorem exists_normalizedOn (p : Layout J) (W : Set J) (r : J → J → Prop)
    (priority : J → ℕ) (hp : p.Respects r) :
    ∃ q : Layout J, p.FixedOutside q W ∧ q.NormalizedOn W r priority := by
  classical
  let candidates : Finset (Layout J) := Finset.univ.filter
    (fun q => q.Respects r ∧ p.FixedOutside q W)
  have hne : candidates.Nonempty := ⟨p, by simp [candidates, hp, Layout.FixedOutside.refl]⟩
  obtain ⟨q, hq, hmin⟩ := candidates.exists_min_image (fun q => q.signature priority) hne
  have hq' : q.Respects r ∧ p.FixedOutside q W := by simpa [candidates] using hq
  refine ⟨q, hq'.2, hq'.1, ?_⟩
  intro u hu hqu
  exact hmin u (by simp [candidates, hu, hq'.2.trans hqu])

theorem normalizedOn_no_improvement {p q : Layout J} {W : Set J}
    {r : J → J → Prop} {priority : J → ℕ} (hp : p.NormalizedOn W r priority)
    (hq : q.Respects r) (hfix : p.FixedOutside q W)
    (i : Fin (Fintype.card J))
    (hbefore : ∀ j, j < i → priority (q.symm j) = priority (p.symm j))
    (hi : priority (q.symm i) < priority (p.symm i)) : False := by
  have hlt : q.signature priority < p.signature priority :=
    ofFn_lt_of_first_difference _ _ i hbefore hi
  exact (not_lt_of_ge (hp.2 q hq hfix)) hlt

theorem exchange_fixedOutside [DecidableEq J] {p : Layout J} {W : Set J}
    {x y : J} (hx : x ∈ W) (hy : y ∈ W) : p.FixedOutside (p.exchange x y) W := by
  intro z hz
  have hzx : z ≠ x := fun e => hz (e ▸ hx)
  have hzy : z ≠ y := fun e => hz (e ▸ hy)
  simp [Layout.exchange, Equiv.swap_apply_of_ne_of_ne hzx hzy]

theorem normalizedOn_prefix_no_exchange [DecidableEq J]
    {p q : Layout J} {W : Set J} {r : J → J → Prop} {priority : J → ℕ}
    (hp : p.NormalizedOn W r priority) (hfix : p.FixedOutside q W)
    {x y : J} (hx : x ∈ W) (hy : y ∈ W)
    (hprefix : ∀ j, j ≤ p y → q.symm j = p.symm j)
    (ht : q.time y < q.time x) (hbetter : priority x < priority y)
    (hswap : (q.exchange x y).Respects r) : False := by
  have hqy : q y = p y := by
    have he := hprefix (p y) le_rfl
    simp only [p.symm_apply_apply] at he
    exact (congrArg q he).symm.trans (q.apply_symm_apply _)
  have hpos : p y < q x := by
    change (p y).val < (q x).val
    dsimp [Layout.time] at ht
    rw [hqy] at ht
    omega
  apply normalizedOn_no_improvement hp hswap
    (hfix.trans (exchange_fixedOutside hx hy)) (p y)
  · intro j hj
    have hpy := hprefix j hj.le
    have hny : q.symm j ≠ y := by
      intro e
      have he : j = p y := by simpa [hqy] using congrArg q e
      exact (ne_of_lt hj) he
    have hnx : q.symm j ≠ x := by
      intro e
      have he : j = q x := by simpa using congrArg q e
      rw [he] at hj
      exact (not_lt_of_ge hpos.le) hj
    change priority ((Equiv.swap x y) (q.symm j)) = priority (p.symm j)
    rw [Equiv.swap_apply_of_ne_of_ne hnx hny, hpy]
  · have hpy := hprefix (p y) le_rfl
    simp only [p.symm_apply_apply] at hpy
    simpa [Layout.exchange, hpy] using hbetter

theorem normalizedOn_local_obstruction {p : Layout J} {W : Finset J}
    {a b : ℕ} {r : J → J → Prop} {priority : J → ℕ}
    (hp : p.NormalizedOn (W : Set J) r priority)
    (hW : ∀ z, z ∈ W ↔ a < p.time z ∧ p.time z < b) :
    LocalObstruction W r p.time priority := by
  classical
  intro x hx y hy htyx hbetter hpred
  by_contra hn
  have hsucc : ∀ v, r y v → p.time x < p.time v := by
    intro v hyv
    have hyvTime := hp.1 y v hyv
    by_cases hv : v ∈ W
    · by_contra h
      exact hn ⟨v, hv, hyv, by omega⟩
    · have hnt : ¬(a < p.time v ∧ p.time v < b) := fun h => hv ((hW v).mpr h)
      have hxt := (hW x).mp hx
      have hyt := (hW y).mp hy
      omega
  have hready : ∀ u, r u x → p.time u < p.time y := by
    intro u hux
    by_cases hu : u ∈ W
    · exact hpred u hu hux
    · have huxTime := hp.1 u x hux
      have hnt : ¬(a < p.time u ∧ p.time u < b) := fun h => hu ((hW u).mpr h)
      have hxt := (hW x).mp hx
      have hyt := (hW y).mp hy
      omega
  exact normalizedOn_prefix_no_exchange hp (Layout.FixedOutside.refl p _)
    hx hy (fun _ _ => rfl) htyx hbetter (respects_exchange hp.1 x y htyx hready hsucc)

end IntervalNormalization
end ThreeMachine.Structure

namespace ThreeMachine.Structure

abbrev Triple (J : Type) := {Z : Finset J // Z.card = 3}

inductive Boundary (J : Type)
  | left
  | actual (Z : Triple J)
  | right

namespace Boundary
variable {J : Type}

def pred (r : J → J → Prop) : Boundary J → Set J
  | .left => ∅
  | .actual Z => {x | ∃ y ∈ Z.val, r x y}
  | .right => Set.univ

def desc (r : J → J → Prop) : Boundary J → Set J
  | .left => Set.univ
  | .actual Z => {x | ∃ y ∈ Z.val, r y x}
  | .right => ∅

def weakPred (r : J → J → Prop) : Boundary J → Set J
  | .left => ∅
  | .actual Z => pred r (.actual Z) ∪ (Z.val : Set J)
  | .right => Set.univ

def weakDesc (r : J → J → Prop) : Boundary J → Set J
  | .left => Set.univ
  | .actual Z => desc r (.actual Z) ∪ (Z.val : Set J)
  | .right => ∅

def reverse : Boundary J → Boundary J
  | .left => .right
  | .actual Z => .actual Z
  | .right => .left

@[simp] theorem reverse_reverse (B : Boundary J) : B.reverse.reverse = B := by cases B <;> rfl

@[simp] theorem pred_reverse (r : J → J → Prop) (B : Boundary J) :
    B.reverse.pred (fun x y => r y x) = B.desc r := by cases B <;> rfl

@[simp] theorem desc_reverse (r : J → J → Prop) (B : Boundary J) :
    B.reverse.desc (fun x y => r y x) = B.pred r := by cases B <;> rfl

@[simp] theorem weakPred_reverse (r : J → J → Prop) (B : Boundary J) :
    B.reverse.weakPred (fun x y => r y x) = B.weakDesc r := by cases B <;> rfl

@[simp] theorem weakDesc_reverse (r : J → J → Prop) (B : Boundary J) :
    B.reverse.weakDesc (fun x y => r y x) = B.weakPred r := by cases B <;> rfl

theorem pred_downset {r : J → J → Prop}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (B : Boundary J) :
    GlobalDownset r (B.pred r) := by
  intro x y hxy hy
  cases B with
  | left => exact hy.elim
  | right => trivial
  | actual Z =>
      obtain ⟨z, hz, hyz⟩ := hy
      exact ⟨z, hz, htrans hxy hyz⟩

theorem desc_upset {r : J → J → Prop}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (B : Boundary J) :
    GlobalUpset r (B.desc r) := by
  intro x y hxy hx
  cases B with
  | left => trivial
  | right => exact hx.elim
  | actual Z =>
      obtain ⟨z, hz, hzx⟩ := hx
      exact ⟨z, hz, htrans hzx hxy⟩

theorem weakPred_downset {r : J → J → Prop}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (B : Boundary J) :
    GlobalDownset r (B.weakPred r) := by
  intro x y hxy hy
  cases B with
  | left => exact hy.elim
  | right => trivial
  | actual Z =>
      rcases hy with h | h
      · exact Or.inl (pred_downset htrans (.actual Z) hxy h)
      · exact Or.inl ⟨y, h, hxy⟩

theorem weakDesc_upset {r : J → J → Prop}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (B : Boundary J) :
    GlobalUpset r (B.weakDesc r) := by
  intro x y hxy hx
  cases B with
  | left => trivial
  | right => exact hx.elim
  | actual Z =>
      rcases hx with h | h
      · exact Or.inl (desc_upset htrans (.actual Z) hxy h)
      · exact Or.inl ⟨x, h, hxy⟩

def At (time : J → ℕ) (T : ℕ) : Boundary J → ℕ → Prop
  | .left, s => s = 0
  | .actual Z, s => 1 ≤ s ∧ s ≤ T ∧ ∀ x, x ∈ Z.val ↔ time x = s
  | .right, s => s = T + 1

theorem pred_time {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {B : Boundary J}
    (hrespect : ∀ u v, r u v → time u < time v)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T) (hB : B.At time T s)
    {x : J} (hx : x ∈ B.pred r) : time x < s := by
  cases B with
  | left => exact hx.elim
  | right => have := (hbound x).2; dsimp [At] at hB; omega
  | actual Z =>
      obtain ⟨y, hy, hxy⟩ := hx
      have he := (hB.2.2 y).mp hy
      have := hrespect x y hxy
      omega

theorem desc_time {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {B : Boundary J}
    (hrespect : ∀ u v, r u v → time u < time v)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T) (hB : B.At time T s)
    {x : J} (hx : x ∈ B.desc r) : s < time x := by
  cases B with
  | left => have := (hbound x).1; dsimp [At] at hB; omega
  | right => exact hx.elim
  | actual Z =>
      obtain ⟨y, hy, hyx⟩ := hx
      have he := (hB.2.2 y).mp hy
      have := hrespect y x hyx
      omega

theorem weakPred_time {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {B : Boundary J}
    (hrespect : ∀ u v, r u v → time u < time v)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T) (hB : B.At time T s)
    {x : J} (hx : x ∈ B.weakPred r) : time x ≤ s := by
  cases B with
  | left => exact hx.elim
  | right => have := (hbound x).2; dsimp [At] at hB; omega
  | actual Z =>
      rcases hx with h | h
      · exact (pred_time hrespect hbound hB h).le
      · exact ((hB.2.2 x).mp h).le

theorem weakDesc_time {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {B : Boundary J}
    (hrespect : ∀ u v, r u v → time u < time v)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T) (hB : B.At time T s)
    {x : J} (hx : x ∈ B.weakDesc r) : s ≤ time x := by
  cases B with
  | left => dsimp [At] at hB; omega
  | right => exact hx.elim
  | actual Z =>
      rcases hx with h | h
      · exact (desc_time hrespect hbound hB h).le
      · exact ((hB.2.2 x).mp h).ge

theorem mem_weak_at_time {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {B : Boundary J}
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T) (hB : B.At time T s)
    {x : J} (hx : time x = s) : x ∈ B.weakPred r ∧ x ∈ B.weakDesc r := by
  cases B with
  | left => have := (hbound x).1; dsimp [At] at hB; omega
  | right => have := (hbound x).2; dsimp [At] at hB; omega
  | actual Z => exact ⟨Or.inr ((hB.2.2 x).mpr hx), Or.inr ((hB.2.2 x).mpr hx)⟩

theorem actual_pred_eq {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {Z : Triple J}
    (hZ : (Boundary.actual Z).At time T s) :
    (Boundary.actual Z).pred r = PredAt r time s := by
  ext x
  simp only [pred, PredAt, Set.mem_ofPred_eq, hZ.2.2]

theorem actual_desc_eq {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {Z : Triple J}
    (hZ : (Boundary.actual Z).At time T s) :
    (Boundary.actual Z).desc r = DescAt r time s := by
  ext x
  simp only [desc, DescAt, Set.mem_ofPred_eq, hZ.2.2]

end Boundary

inductive Formula (A : Type)
  | leaf (atom : A) (negative : Bool)
  | conj (p q : Formula A)
  | disj (p q : Formula A)

namespace Formula
variable {A J : Type}

def leaves : Formula A → ℕ
  | .leaf _ _ => 1
  | .conj p q | .disj p q => p.leaves + q.leaves

def eval (atoms : A → Set J) : Formula A → Set J
  | .leaf a false => atoms a
  | .leaf a true => (atoms a)ᶜ
  | .conj p q => p.eval atoms ∩ q.eval atoms
  | .disj p q => p.eval atoms ∪ q.eval atoms

def negate : Formula A → Formula A
  | .leaf a b => .leaf a (!b)
  | .conj p q => .disj p.negate q.negate
  | .disj p q => .conj p.negate q.negate

@[simp] theorem leaves_negate (p : Formula A) : p.negate.leaves = p.leaves := by
  induction p with
  | leaf a b => cases b <;> rfl
  | conj p q hp hq | disj p q hp hq => simp [negate, leaves, hp, hq]

@[simp] theorem eval_negate (atoms : A → Set J) (p : Formula A) :
    p.negate.eval atoms = (p.eval atoms)ᶜ := by
  induction p with
  | leaf a b => cases b <;> simp [negate, eval]
  | conj p q hp hq =>
      ext x
      simp only [negate, eval, hp, hq, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
      tauto
  | disj p q hp hq => simp [negate, eval, hp, hq]

theorem leaves_pos (p : Formula A) : 0 < p.leaves := by
  induction p with
  | leaf => exact Nat.zero_lt_one
  | conj p q hp hq | disj p q hp hq => dsimp [leaves]; omega

end Formula

def Described {A J : Type} (atoms : A → Set J) (W : Set J) (k : ℕ) : Prop :=
  ∃ p : Formula A, p.eval atoms = W ∧ p.leaves ≤ k

namespace Described
variable {A J : Type} {atoms : A → Set J} {W U : Set J} {k l : ℕ}

theorem mono (h : Described atoms W k) (hkl : k ≤ l) : Described atoms W l := by
  obtain ⟨p, hp, hk⟩ := h
  exact ⟨p, hp, hk.trans hkl⟩

theorem atom (a : A) : Described atoms (atoms a) 1 := ⟨.leaf a false, rfl, le_rfl⟩

theorem compl (h : Described atoms W k) : Described atoms Wᶜ k := by
  obtain ⟨p, hp, hk⟩ := h
  exact ⟨p.negate, by simp [hp], by simpa using hk⟩

theorem inter (hW : Described atoms W k) (hU : Described atoms U l) :
    Described atoms (W ∩ U) (k + l) := by
  obtain ⟨p, hp, hk⟩ := hW
  obtain ⟨q, hq, hl⟩ := hU
  exact ⟨.conj p q, by simp [Formula.eval, hp, hq], Nat.add_le_add hk hl⟩

theorem union (hW : Described atoms W k) (hU : Described atoms U l) :
    Described atoms (W ∪ U) (k + l) := by
  obtain ⟨p, hp, hk⟩ := hW
  obtain ⟨q, hq, hl⟩ := hU
  exact ⟨.disj p q, by simp [Formula.eval, hp, hq], Nat.add_le_add hk hl⟩

theorem diff (hW : Described atoms W k) (hU : Described atoms U l) :
    Described atoms (W \ U) (k + l) := hW.inter hU.compl

theorem finite_union {ι : Type} (s : Finset ι) (E : ι → Set J) (b : ι → ℕ)
    (hne : s.Nonempty) (hE : ∀ i ∈ s, Described atoms (E i) (b i)) :
    Described atoms {x | ∃ i ∈ s, x ∈ E i} (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hne).elim
  | @insert i s hi ih =>
      by_cases hs : s.Nonempty
      · have hrest := ih hs (fun j hj => hE j (Finset.mem_insert_of_mem hj))
        have hfirst := hE i (Finset.mem_insert_self _ _)
        have he : {x | ∃ j ∈ insert i s, x ∈ E j} = E i ∪ {x | ∃ j ∈ s, x ∈ E j} := by
          ext x
          simp only [Set.mem_ofPred_eq, Finset.mem_insert, Set.mem_union]
          aesop
        rw [he, Finset.sum_insert hi]
        exact hfirst.union hrest
      · have es : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        simpa using hE i (Finset.mem_insert_self i ∅)

end Described
end ThreeMachine.Structure

end

end OAI
