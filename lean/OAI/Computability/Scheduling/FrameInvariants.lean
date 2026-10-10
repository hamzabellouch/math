import OAI.Computability.Scheduling.CutoffSimplification

namespace OAI

section

namespace ThreeMachine.Structure
namespace Layout
variable {J : Type} [Fintype J]

theorem time_bounds (p : Layout J) (hfull : 3 ∣ Fintype.card J) (x : J) :
    1 ≤ p.time x ∧ p.time x ≤ Fintype.card J / 3 := by
  obtain ⟨T, hT⟩ := hfull
  have hp := (p x).isLt
  dsimp [time]
  omega

noncomputable def slot (p : Layout J) (s : ℕ) : Finset J := by
  classical
  exact Finset.univ.filter (fun x => p.time x = s)

@[simp] theorem mem_slot (p : Layout J) (s : ℕ) (x : J) :
    x ∈ p.slot s ↔ p.time x = s := by
  classical
  simp [slot]

theorem card_slot (p : Layout J) (hfull : 3 ∣ Fintype.card J) (s : ℕ)
    (hs : 1 ≤ s) (hsT : s ≤ Fintype.card J / 3) : (p.slot s).card = 3 := by
  classical
  obtain ⟨T, hT⟩ := hfull
  let i : Fin (Fintype.card J) := ⟨3 * (s - 1), by omega⟩
  let j : Fin (Fintype.card J) := ⟨3 * (s - 1) + 1, by omega⟩
  let k : Fin (Fintype.card J) := ⟨3 * (s - 1) + 2, by omega⟩
  apply Finset.card_eq_three.mpr
  refine ⟨p.symm i, p.symm j, p.symm k, ?_, ?_, ?_, ?_⟩
  · intro he
    have hev := congrArg Fin.val (p.symm.injective he)
    dsimp [i, j] at hev
    omega
  · intro he
    have hev := congrArg Fin.val (p.symm.injective he)
    dsimp [i, k] at hev
    omega
  · intro he
    have hev := congrArg Fin.val (p.symm.injective he)
    dsimp [j, k] at hev
    omega
  · ext x
    simp only [mem_slot, Finset.mem_insert, Finset.mem_singleton]
    have hxi : x = p.symm i ↔ (p x).val = 3 * (s - 1) := by
      rw [Equiv.eq_symm_apply]
      exact Fin.ext_iff
    have hxj : x = p.symm j ↔ (p x).val = 3 * (s - 1) + 1 := by
      rw [Equiv.eq_symm_apply]
      exact Fin.ext_iff
    have hxk : x = p.symm k ↔ (p x).val = 3 * (s - 1) + 2 := by
      rw [Equiv.eq_symm_apply]
      exact Fin.ext_iff
    rw [hxi, hxj, hxk]
    dsimp [time]
    omega

noncomputable def triple (p : Layout J) (hfull : 3 ∣ Fintype.card J)
    (s : ℕ) (hs : 1 ≤ s) (hsT : s ≤ Fintype.card J / 3) : Triple J :=
  ⟨p.slot s, p.card_slot hfull s hs hsT⟩

theorem triple_at (p : Layout J) (hfull : 3 ∣ Fintype.card J)
    (s : ℕ) (hs : 1 ≤ s) (hsT : s ≤ Fintype.card J / 3) :
    (Boundary.actual (p.triple hfull s hs hsT)).At p.time (Fintype.card J / 3) s := by
  exact ⟨hs, hsT, fun x => p.mem_slot s x⟩

def reverse (p : Layout J) : Layout J := p.trans Fin.revPerm

@[simp] theorem reverse_reverse (p : Layout J) : p.reverse.reverse = p := by
  ext x
  simp [reverse]

theorem reverse_time (p : Layout J) (hfull : 3 ∣ Fintype.card J) (x : J) :
    p.reverse.time x = Fintype.card J / 3 + 1 - p.time x := by
  obtain ⟨T, hT⟩ := hfull
  have hp := (p x).isLt
  change (Fintype.card J - ((p x).val + 1)) / 3 + 1 =
    Fintype.card J / 3 + 1 - ((p x).val / 3 + 1)
  omega

theorem reverse_respects {p : Layout J} {r : J → J → Prop}
    (hfull : 3 ∣ Fintype.card J) (hp : p.Respects r) :
    p.reverse.Respects (fun x y => r y x) := by
  intro x y hyx
  rw [p.reverse_time hfull, p.reverse_time hfull]
  have hxy := hp y x hyx
  have hx := p.time_bounds hfull x
  have hy := p.time_bounds hfull y
  omega

theorem reverse_full {p : Layout J} {r : J → J → Prop} (hp : p.Full r) :
    p.reverse.Full (fun x y => r y x) := ⟨hp.1, reverse_respects hp.1 hp.2⟩

theorem FixedOutside.reverse {p q : Layout J} {W : Set J}
    (h : p.FixedOutside q W) : p.reverse.FixedOutside q.reverse W := by
  intro x hx
  simp [Layout.reverse, h x hx]

end Layout

namespace Boundary
variable {J : Type} [Fintype J]

theorem at_reverse {p : Layout J} (hfull : 3 ∣ Fintype.card J)
    {B : Boundary J} {s : ℕ} (h : B.At p.time (Fintype.card J / 3) s) :
    B.reverse.At p.reverse.time (Fintype.card J / 3) (Fintype.card J / 3 + 1 - s) := by
  cases B with
  | left => dsimp [At] at h; subst s; rfl
  | right => dsimp [At] at h; subst s; simp [reverse, At]
  | actual Z =>
      dsimp only [At] at h
      refine ⟨by omega, by omega, ?_⟩
      intro x
      rw [h.2.2, p.reverse_time hfull]
      have hx := p.time_bounds hfull x
      omega

end Boundary

end ThreeMachine.Structure

namespace ThreeMachine.Structure
section IntervalHelpers
variable {J : Type} [Fintype J]

theorem Layout.FixedOutside.window {p q : Layout J} {W : Set J} {a b : ℕ}
    (h : p.FixedOutside q W) (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b) :
    ∀ x, x ∈ W ↔ x ∈ Window q.time a b := by
  intro x
  constructor
  · exact h.time_range (fun z hz => (hW z).mp hz)
  · intro hx
    by_contra hn
    have he := h.time hn
    apply hn
    apply (hW x).mpr
    change a < q.time x ∧ q.time x < b at hx
    change a < p.time x ∧ p.time x < b
    simpa only [he] using hx

theorem Layout.FixedOutside.boundary {p q : Layout J} {W : Set J} {a b s T : ℕ}
    {B : Boundary J} (h : p.FixedOutside q W)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hs : s ≤ a ∨ b ≤ s) (hB : B.At p.time T s) : B.At q.time T s := by
  cases B with
  | left => exact hB
  | right => exact hB
  | actual Z =>
      refine ⟨hB.1, hB.2.1, ?_⟩
      intro x
      by_cases hx : x ∈ W
      · have hp := (hW x).mp hx
        have hq := (h.window hW x).mp hx
        have hnp : p.time x ≠ s := by rcases hs with hs | hs <;> dsimp [Window] at hp <;> omega
        have hnq : q.time x ≠ s := by rcases hs with hs | hs <;> dsimp [Window] at hq <;> omega
        rw [hB.2.2]
        exact iff_of_false hnp hnq
      · rw [hB.2.2, h.time hx]

theorem PastInvariant.reorder {r : J → J → Prop} {p q : Layout J}
    {K : GlobalList J} {A : Boundary J} {a b : ℕ} {W : Set J}
    (hpast : PastInvariant r p.time K A a) (hfix : p.FixedOutside q W)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b) :
    PastInvariant r q.time K A a := by
  intro x hx htime
  have hnW : x ∉ W := by
    intro hw
    have h := ((hfix.window hW) x).mp hw
    exact (not_lt_of_ge htime) h.1
  have ht : p.time x = q.time x := (hfix.time hnW).symm
  exact hpast x hx (ht ▸ htime)

def SwapInvariant [DecidableEq J] (r : J → J → Prop) (p : Layout J)
    (W : Set J) (K : GlobalList J) (rank : J → ℕ) (A : Boundary J) (a : ℕ) : Prop :=
  ∀ q : Layout J, p.FixedOutside q W → q.Respects r →
    ∀ x ∈ W, x ∉ A.desc r → ∀ y, q.time y = a → y ∈ K.Qual →
      K.KeyLT rank x y → ¬(q.exchange x y).Respects r

theorem SwapInvariant.reorder [DecidableEq J] {r : J → J → Prop} {p q : Layout J}
    {W : Set J} {K : GlobalList J} {rank : J → ℕ} {A : Boundary J} {a : ℕ}
    (h : SwapInvariant r p W K rank A a) (hfix : p.FixedOutside q W) :
    SwapInvariant r q W K rank A a := by
  intro u hqu hu x hx hnx y hy hyq hkey
  exact h u (hfix.trans hqu) hu x hx hnx y hy hyq hkey

theorem ideal_has_separator_interval {r : J → J → Prop} {S : Set J}
    (p : Layout J) (hp : p.Full r) {W : Finset J} {a b : ℕ}
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b) (hne : W.Nonempty)
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hideal : IdealOn W r S) :
    ∃ q : Layout J, p.FixedOutside q (W : Set J) ∧ q.Full r ∧
      ∃ t, a < t ∧ t < b ∧ Separator W r q.time S t := by
  classical
  let priority := fun x : J => if x ∈ S then (p x).val else Fintype.card J + (p x).val
  have hprefix : PrefixOn W priority S := by
    intro x _ hx y _ hy
    simp only [priority, ite_eq_left hx, ite_eq_right hy]
    have := (p x).isLt
    omega
  obtain ⟨q, hfix, hq⟩ := exists_normalizedOn p W r priority hp.2
  have hWq : ∀ x, x ∈ W ↔ x ∈ Window q.time a b := hfix.window hW
  obtain ⟨x, hx, hmin⟩ := W.exists_min_image q.time hne
  have hclosed : SlotClosed W q.time := by
    intro z hz y he
    apply (hWq y).mpr
    have hzt := (hWq z).mp hz
    change a < q.time z ∧ q.time z < b at hzt
    change a < q.time y ∧ q.time y < b
    simpa only [he] using hzt
  have hbefore : EarlierHigh W r q.time S (q.time x) := by
    intro z hz ht _
    have := hmin z hz
    omega
  obtain ⟨t, _hst, hpath, hsep⟩ := walk_to_separator htrans hq.1 hclosed
    (Or.inl ⟨x, hx, rfl⟩) hideal hprefix
    (normalizedOn_local_obstruction hq hWq) hbefore
  have ht : ∃ z ∈ W, q.time z = t := by
    rcases hpath.endpoint with he | ⟨z, hz, hzt⟩
    · exact ⟨x, hx, he.symm⟩
    · exact ⟨z, hz, hzt⟩
  obtain ⟨z, hz, hzt⟩ := ht
  have hztBounds := (hWq z).mp hz
  change a < q.time z ∧ q.time z < b at hztBounds
  refine ⟨q, hfix, ⟨hp.1, hq.1⟩, t, ?_, ?_, hsep⟩ <;> omega

end IntervalHelpers
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section BoundaryWalk
variable {J : Type} [Fintype J]

theorem exception_global_ready {r : J → J → Prop} {p : Layout J}
    {E : Finset J} {a v : ℕ} {S : Set J} {x : J}
    (htrans : ∀ ⦃u z w⦄, r u z → r z w → r u w) (hp : p.Respects r)
    (hE : ∀ z, z ∈ E ↔ a < p.time z ∧ p.time z < v)
    (hideal : IdealOn E r S) (hx : Exception E r p.time S a x) :
    ∀ u, r u x → p.time u < a := by
  intro u hux
  have htx := hp u x hux
  have hxt := (hE x).mp hx.mem
  by_contra hn
  have hau : a ≤ p.time u := by omega
  rcases hau.eq_or_lt with he | hl
  · exact hx.not_desc ⟨u, he.symm, hux⟩
  · have hu : u ∈ E := (hE u).mpr ⟨hl, htx.trans hxt.2⟩
    have := exception_ready htrans hp hideal hx u hu hux
    omega

omit [Fintype J] in

theorem advance_carry_descendant {r : J → J → Prop} {time priority : J → ℕ}
    {E : Finset J} {H S : Set J} {a v s : ℕ} {x y : J}
    (htrans : ∀ ⦃u z w⦄, r u z → r z w → r u w)
    (hrespect : ∀ u z, r u z → time u < time z)
    (hE : ∀ z, z ∈ E ↔ a < time z ∧ time z < v)
    (hH : GlobalUpset r H) (hhigh : ∀ z ∈ E, z ∈ H → z ∉ S)
    (hideal : IdealOn E r S) (hprefix : PrefixOn E priority S)
    (hnorm : LocalObstruction E r time priority)
    (has : a ≤ s) (hx : Exception E r time S s x)
    (hfirst : s = a → ∀ z ∈ H, time z = a → ∃ u ∈ E, r z u ∧ time u ≤ time x)
    (hyH : y ∈ H) (hys : time y = s) :
    ∃ z ∈ E, time z = time x ∧ r y z ∧ z ∈ H := by
  have hready := exception_ready htrans hrespect hideal hx
  have hforce : ∀ z ∈ E, z ∉ S → s ≤ time z → time z < time x →
      ∃ u ∈ E, r z u ∧ time u ≤ time x := by
    intro z hz hnS hsz hzx
    exact hnorm x hx.mem z hz hzx (hprefix x hx.mem hx.low z hz hnS)
      (fun u hu hux => (hready u hu hux).trans_le hsz)
  have hsucc : ∃ u ∈ E, r y u ∧ time u ≤ time x := by
    by_cases hsa : s = a
    · exact hfirst hsa y hyH (hys.trans hsa)
    · have hyE : y ∈ E := (hE y).mpr
        ⟨by omega, by have := (hE x).mp hx.mem; have := hx.later; omega⟩
      exact hforce y hyE (hhigh y hyE hyH) (by omega) (by have := hx.later; omega)
  obtain ⟨u, hu, hyu, hut⟩ := hsucc
  have huH := hH hyu hyH
  have hsu : s ≤ time u := by have := hrespect y u hyu; omega
  obtain ⟨z, hz, hzt, huz, _hnS⟩ := trace_to_slot htrans hrespect hideal hforce
    u hu (hhigh u hu huH) hsu hut
  have hyz : r y z := by
    rcases huz with e | hur
    · simpa [e] using hyu
    · exact htrans hyu hur
  exact ⟨z, hz, hzt, hyz, hH hyz hyH⟩

theorem first_boundary_force [DecidableEq J]
    {r : J → J → Prop} {p : Layout J} {E : Finset J} {a v : ℕ}
    {S H : Set J} {x : J}
    (htrans : ∀ ⦃u z w⦄, r u z → r z w → r u w) (hp : p.Respects r)
    (hE : ∀ z, z ∈ E ↔ a < p.time z ∧ p.time z < v)
    (hideal : IdealOn E r S) (hx : Exception E r p.time S a x)
    (hno : ∀ y ∈ H, p.time y = a → ¬(p.exchange x y).Respects r) :
    ∀ y ∈ H, p.time y = a → ∃ u ∈ E, r y u ∧ p.time u ≤ p.time x := by
  have hready : ∀ u, r u x → p.time u < a :=
    exception_global_ready htrans hp hE hideal hx
  intro y hy hya
  by_contra hn
  have hsucc : ∀ u, r y u → p.time x < p.time u := by
    intro u hyu
    by_contra hntu
    have hxv := ((hE x).mp hx.mem).2
    have hyut := hp y u hyu
    have huE : u ∈ E := (hE u).mpr ⟨by omega, by omega⟩
    exact hn ⟨u, huE, hyu, by omega⟩
  have hyx : p.time y < p.time x := by have := hx.later; omega
  exact hno y hy hya (respects_exchange hp x y hyx (fun u hur => by
    have := hready u hur; omega) hsucc)

end BoundaryWalk
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section VaryingWalk
variable {J : Type}

inductive CutoffWalk (E : Finset J) (r : J → J → Prop) (time priority : J → ℕ)
    (Sfinal : Set J) (a : ℕ) : ℕ → Prop
  | refl : CutoffWalk E r time priority Sfinal a a
  | step {s : ℕ} {x : J} {U : Set J}
      (prev : CutoffWalk E r time priority Sfinal a s)
      (ideal : IdealOn E r U) (isPrefix : PrefixOn E priority U)
      (below : ∀ z ∈ E, z ∈ U → z ∈ Sfinal)
      (exception : Exception E r time U s x) :
      CutoffWalk E r time priority Sfinal a (time x)

theorem CutoffWalk.le {E : Finset J} {r : J → J → Prop} {time priority : J → ℕ}
    {S : Set J} {a t : ℕ} (h : CutoffWalk E r time priority S a t) : a ≤ t := by
  induction h with
  | refl => exact le_rfl
  | step _ _ _ _ hx ih => exact ih.trans hx.later.le

theorem CutoffWalk.mono {E : Finset J} {r : J → J → Prop} {time priority : J → ℕ}
    {S S' : Set J} {a t : ℕ} (h : CutoffWalk E r time priority S a t)
    (hsub : ∀ z ∈ E, z ∈ S → z ∈ S') : CutoffWalk E r time priority S' a t := by
  induction h with
  | refl => exact .refl
  | step _ hi hp hb hx ih => exact .step ih hi hp (fun z hz hu => hsub z hz (hb z hz hu)) hx

theorem CutoffWalk.trans_advance {E : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S U : Set J} {a s t : ℕ}
    (h : CutoffWalk E r time priority S a s) (hp : AdvancePath E r time U s t)
    (hi : IdealOn E r U) (hprefix : PrefixOn E priority U)
    (hbelow : ∀ z ∈ E, z ∈ U → z ∈ S) :
    CutoffWalk E r time priority S a t := by
  induction hp with
  | refl => exact h
  | step _ hx ih => exact .step ih hi hprefix hbelow hx

theorem CutoffWalk.carry {E : Finset J} {r : J → J → Prop} {time priority : J → ℕ}
    {S H : Set J} {a v t : ℕ}
    (htrans : ∀ ⦃u z w⦄, r u z → r z w → r u w)
    (hrespect : ∀ u z, r u z → time u < time z)
    (hE : ∀ z, z ∈ E ↔ a < time z ∧ time z < v)
    (hH : GlobalUpset r H) (hhigh : ∀ z ∈ E, z ∈ H → z ∉ S)
    (hnorm : LocalObstruction E r time priority)
    (hfirst : ∀ U, IdealOn E r U → PrefixOn E priority U →
      (∀ z ∈ E, z ∈ U → z ∈ S) → ∀ x, Exception E r time U a x →
      ∀ y ∈ H, time y = a → ∃ u ∈ E, r y u ∧ time u ≤ time x)
    (hwalk : CutoffWalk E r time priority S a t) :
    ∀ y ∈ H, time y = a → ∃ z, time z = t ∧ (z = y ∨ r y z) ∧ z ∈ H := by
  induction hwalk with
  | refl => exact fun y hy ht => ⟨y, ht, Or.inl rfl, hy⟩
  | @step s x U prev hi hp hb hx ih =>
    intro y hy hyt
    obtain ⟨z, hzt, hyz, hzH⟩ := ih y hy hyt
    obtain ⟨w, _hw, hwt, hzw, hwH⟩ := advance_carry_descendant htrans hrespect hE hH
      (fun z hz hzH hzU => hhigh z hz hzH (hb z hz hzU)) hi hp hnorm prev.le hx
      (fun hsa => hfirst U hi hp hb x (by simpa only [hsa] using hx)) hzH hzt
    refine ⟨w, hwt, Or.inr ?_, hwH⟩
    rcases hyz with rfl | hyz
    · exact hzw
    · exact htrans hyz hzw

end VaryingWalk

section PastUpdate
variable {J : Type} [Fintype J]

omit [Fintype J] in

theorem Boundary.weakPred_witness {r : J → J → Prop} {time : J → ℕ}
    {T a : ℕ} {A : Boundary J} {x : J}
    (hA : A.At time T a) (ha : a ≤ T) (hx : x ∈ A.weakPred r) :
    ∃ y, time y = a ∧ (x = y ∨ r x y) := by
  cases A with
  | left => exact False.elim hx
  | right => simp only [Boundary.At] at hA; omega
  | actual Z =>
    rcases hx with ⟨y, hy, hxy⟩ | hx
    · exact ⟨y, (hA.2.2 y).mp hy, Or.inr hxy⟩
    · exact ⟨x, (hA.2.2 x).mp hx, Or.inl rfl⟩

theorem past_update {r : J → J → Prop} {p : Layout J} {priority : J → ℕ}
    {E : Finset J} {a v ap : ℕ} {A A' : Boundary J} {K K' : GlobalList J}
    {S H : Set J}
    (hp : p.Full r) (htrans : ∀ ⦃u z w⦄, r u z → r z w → r u w)
    (hA : A.At p.time (Fintype.card J / 3) a)
    (hA' : A'.At p.time (Fintype.card J / 3) ap)
    (ha : a ≤ Fintype.card J / 3) (hap : ap < v)
    (hE : ∀ z, z ∈ E ↔ a < p.time z ∧ p.time z < v)
    (hparent : PastInvariant r p.time K A a)
    (hH : GlobalUpset r H) (hHO : H ⊆ K.Qual)
    (hearly : ∀ z ∈ K'.Qual, p.time z ≤ a → z ∈ H)
    (hhigh : ∀ z ∈ E, z ∈ K'.Qual → z ∉ S)
    (hHhigh : ∀ z ∈ E, z ∈ H → z ∉ S)
    (hsep : A'.Separates r p.time E S ap)
    (hnorm : LocalObstruction E r p.time priority)
    (hfirst : ∀ U, IdealOn E r U → PrefixOn E priority U →
      (∀ z ∈ E, z ∈ U → z ∈ S) → ∀ x, Exception E r p.time U a x →
      ∀ y ∈ H, p.time y = a → ∃ u ∈ E, r y u ∧ p.time u ≤ p.time x)
    (hwalk : CutoffWalk E r p.time priority S a ap) :
    PastInvariant r p.time K' A' ap := by
  intro z hz hzt
  by_cases hae : p.time z ≤ a
  · have hzH := hearly z hz hae
    obtain ⟨y, hya, hzy⟩ := Boundary.weakPred_witness hA ha (hparent z (hHO hzH) hae)
    have hyH : y ∈ H := by
      rcases hzy with rfl | hzy
      · exact hzH
      · exact hH hzy hzH
    obtain ⟨w, hwt, hyw, _hwH⟩ := hwalk.carry htrans hp.2 hE hH hHhigh hnorm hfirst y hyH hya
    have hwmem : w ∈ A'.weakPred r :=
      (Boundary.mem_weak_at_time (p.time_bounds hp.1) hA' hwt).1
    rcases hzy with rfl | hzy
    · rcases hyw with rfl | hyw
      · exact hwmem
      · exact Boundary.weakPred_downset htrans A' hyw hwmem
    · have hzw : r z w := by
        rcases hyw with rfl | hyw
        · exact hzy
        · exact htrans hzy hyw
      exact Boundary.weakPred_downset htrans A' hzw hwmem
  · have hzE := (hE z).mpr ⟨by omega, by omega⟩
    rcases hzt.eq_or_lt with he | hl
    · exact (Boundary.mem_weak_at_time (p.time_bounds hp.1) hA' he).1
    · exact A'.pred_subset_weakPred r (hsep.1 z hzE hl (hhigh z hzE hz))

end PastUpdate
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section ChildSwaps
variable {J : Type} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
theorem Layout.FixedOutside.earlier_positions {p q : Layout J} {W : Set J} {a b : ℕ}
    (hfix : p.FixedOutside q W) (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    {y : J} (hy : p.time y ≤ a) : ∀ j, j ≤ p y → q.symm j = p.symm j := by
  intro j hj
  have hn : p.symm j ∉ W := by
    intro hmem
    have ht := ((hW _).mp hmem).1
    dsimp [Layout.time] at ht hy
    have hjv : j.val ≤ (p y).val := hj
    simp only [p.apply_symm_apply] at ht
    omega
  apply q.injective
  rw [q.apply_symm_apply, hfix _ hn, p.apply_symm_apply]

theorem swap_from_normalized {r : J → J → Prop} {p : Layout J}
    {E W : Set J} {a b ap bp : ℕ} {A' : Boundary J}
    {K : GlobalList J} {rank priority : J → ℕ}
    (hE : ∀ x, x ∈ E ↔ x ∈ Window p.time a b)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time ap bp)
    (ha : a < ap) (hb : bp ≤ b) (hab : ap < bp)
    (hnorm : p.NormalizedOn E r priority)
    (hqual : ∀ x ∈ W, x ∉ A'.desc r → x ∈ K.Qual)
    (hkeys : ∀ x ∈ W, x ∈ K.Qual → ∀ y, p.time y = ap → y ∈ K.Qual →
      K.KeyLT rank x y → priority x < priority y) :
    SwapInvariant r p W K rank A' ap := by
  intro q hfix _hq x hx hnx y hy hyq hkey hswap
  have hWx := (hfix.window hW x).mp hx
  have hnWy : y ∉ W := by
    intro hw
    have ht := ((hfix.window hW) y).mp hw
    exact (lt_irrefl ap) (hy ▸ ht.1)
  have hpya : p.time y = ap := (hfix.time hnWy).symm.trans hy
  have hWE : W ⊆ E := by
    intro z hz
    have ht := (hW z).mp hz
    exact (hE z).mpr ⟨ha.trans ht.1, ht.2.trans_le hb⟩
  have hyE : y ∈ E := (hE y).mpr ⟨by omega, by omega⟩
  exact normalizedOn_prefix_no_exchange hnorm (hfix.mono hWE) (hWE hx) hyE
    (hfix.earlier_positions hW hpya.le) (by have := hWx.1; omega)
    (hkeys x hx (hqual x hx hnx) y hpya hyq hkey) hswap

theorem swap_inherited {r : J → J → Prop} {p : Layout J}
    {W W' : Set J} {K K' : GlobalList J} {rank : J → ℕ} {A : Boundary J} {a : ℕ}
    (hparent : SwapInvariant r p W K rank A a) (hsub : W' ⊆ W)
    (hqual : ∀ y ∈ K'.Qual, y ∈ K.Qual)
    (hkeys : ∀ x ∈ W', x ∉ A.desc r → ∀ y ∈ K'.Qual,
      K'.KeyLT rank x y → K.KeyLT rank x y) :
    SwapInvariant r p W' K' rank A a := by
  intro q hfix hq x hx hnx y hy hyq hkey
  exact hparent q (hfix.mono hsub) hq x (hsub hx) hnx y hy
    (hqual y hyq) (hkeys x hx hnx y hyq hkey)

theorem swap_prune {r : J → J → Prop} {p : Layout J}
    {W : Set J} {K : GlobalList J} {rank : J → ℕ} {A : Boundary J} {a : ℕ}
    (hparent : SwapInvariant r p W K rank A a) :
    SwapInvariant r p W (K.prune W) rank A a := by
  intro q hfix hq x hx hnx y hy hyq hkey
  exact hparent q hfix hq x hx hnx y hy (K.prune_qual_subset W hyq)
    (GlobalList.prune_key hx hkey)

end ChildSwaps
end ThreeMachine.Structure

end

end OAI
