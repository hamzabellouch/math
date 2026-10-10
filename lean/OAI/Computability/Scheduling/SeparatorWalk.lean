import OAI.Computability.Scheduling.Model

namespace OAI

section

namespace ThreeMachine
namespace Structure

abbrev Layout (J : Type) [Fintype J] := J ≃ Fin (Fintype.card J)

def Layout.time {J : Type} [Fintype J] (p : Layout J) (x : J) : ℕ :=
  (p x).val / 3 + 1

def Layout.Respects {J : Type} [Fintype J] (p : Layout J)
    (r : J → J → Prop) : Prop :=
  ∀ x y, r x y → p.time x < p.time y

def Layout.Full {J : Type} [Fintype J] (p : Layout J)
    (r : J → J → Prop) : Prop :=
  3 ∣ Fintype.card J ∧ p.Respects r

def Layout.signature {J : Type} [Fintype J] (p : Layout J)
    (priority : J → ℕ) : List ℕ :=
  List.ofFn (fun i => priority (p.symm i))

def Layout.Normalized {J : Type} [Fintype J] (p : Layout J)
    (r : J → J → Prop) (priority : J → ℕ) : Prop :=
  p.Respects r ∧ ∀ q : Layout J, q.Respects r →
    p.signature priority ≤ q.signature priority

theorem exists_normalized {J : Type} [Fintype J] (r : J → J → Prop)
    (priority : J → ℕ) (p : Layout J) (hp : p.Respects r) :
    ∃ q : Layout J, q.Normalized r priority := by
  classical
  let candidates : Finset (Layout J) := Finset.univ.filter (fun q => q.Respects r)
  have hc : candidates.Nonempty := ⟨p, by simp [candidates, hp]⟩
  obtain ⟨q, hq, hmin⟩ := candidates.exists_min_image
    (fun q => q.signature priority) hc
  refine ⟨q, ?_, ?_⟩
  · simpa [candidates] using hq
  · intro q' hq'
    exact hmin q' (by simp [candidates, hq'])

theorem ofFn_lt_of_first_difference {n : ℕ} (f g : Fin n → ℕ)
    (i : Fin n) (hbefore : ∀ j, j < i → f j = g j) (hi : f i < g i) :
    List.ofFn f < List.ofFn g := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    by_cases h0 : i.val = 0
    · have e : i = 0 := Fin.ext h0
      exact List.Lex.rel (by simpa [e] using hi)
    · let j : Fin n := ⟨i.val - 1, by omega⟩
      have ei : j.succ = i := Fin.ext (by dsimp [j]; omega)
      have he : f 0 = g 0 := hbefore 0 (by change 0 < i.val; omega)
      rw [he]
      apply List.Lex.cons
      apply ih (fun k => f k.succ) (fun k => g k.succ) j
      · intro k hk
        apply hbefore k.succ
        rw [← ei]
        exact Fin.succ_lt_succ_iff.mpr hk
      · simpa [ei] using hi

theorem normalized_no_improvement {J : Type} [Fintype J]
    {p q : Layout J} {r : J → J → Prop} {priority : J → ℕ}
    (hp : p.Normalized r priority) (hq : q.Respects r)
    (i : Fin (Fintype.card J))
    (hbefore : ∀ j, j < i → priority (q.symm j) = priority (p.symm j))
    (hi : priority (q.symm i) < priority (p.symm i)) : False := by
  have hlt : q.signature priority < p.signature priority :=
    ofFn_lt_of_first_difference _ _ i hbefore hi
  exact (not_lt_of_ge (hp.2 q hq)) hlt

def Layout.exchange {J : Type} [Fintype J] [DecidableEq J]
    (p : Layout J) (x y : J) : Layout J :=
  (Equiv.swap x y).trans p

@[simp] theorem exchange_time_left {J : Type} [Fintype J] [DecidableEq J]
    (p : Layout J) (x y : J) : (p.exchange x y).time x = p.time y := by
  simp [Layout.time, Layout.exchange]

@[simp] theorem exchange_time_right {J : Type} [Fintype J] [DecidableEq J]
    (p : Layout J) (x y : J) : (p.exchange x y).time y = p.time x := by
  simp [Layout.time, Layout.exchange]

theorem exchange_time_other {J : Type} [Fintype J] [DecidableEq J]
    (p : Layout J) (x y z : J) (hx : z ≠ x) (hy : z ≠ y) :
    (p.exchange x y).time z = p.time z := by
  simp [Layout.time, Layout.exchange, Equiv.swap_apply_of_ne_of_ne hx hy]

theorem respects_exchange {J : Type} [Fintype J] [DecidableEq J]
    {p : Layout J} {r : J → J → Prop} (hp : p.Respects r)
    (x y : J) (hxy : p.time y < p.time x)
    (hpred : ∀ u, r u x → p.time u < p.time y)
    (hsucc : ∀ v, r y v → p.time x < p.time v) :
    (p.exchange x y).Respects r := by
  intro u v huv
  have htime := hp u v huv
  by_cases hux : u = x
  · subst u
    by_cases hvx : v = x
    · subst v
      omega
    by_cases hvy : v = y
    · subst v
      simp only [exchange_time_left, exchange_time_right]
      exact hxy
    rw [exchange_time_left, exchange_time_other p x y v hvx hvy]
    exact hxy.trans htime
  by_cases huy : u = y
  · subst u
    have hav := hsucc v huv
    by_cases hvx : v = x
    · subst v
      omega
    by_cases hvy : v = y
    · subst v
      omega
    rw [exchange_time_right, exchange_time_other p x y v hvx hvy]
    exact hav
  rw [exchange_time_other p x y u hux huy]
  by_cases hvx : v = x
  · subst v
    rw [exchange_time_left]
    exact hpred u huv
  by_cases hvy : v = y
  · subst v
    rw [exchange_time_right]
    exact htime.trans hxy
  rw [exchange_time_other p x y v hvx hvy]
  exact htime

theorem normalized_no_exchange {J : Type} [Fintype J] [DecidableEq J]
    {p : Layout J} {r : J → J → Prop} {priority : J → ℕ}
    (hp : p.Normalized r priority) (x y : J)
    (ht : p.time y < p.time x) (hbetter : priority x < priority y)
    (hswap : (p.exchange x y).Respects r) : False := by
  have hpos : p y < p x := by
    change (p y).val < (p x).val
    dsimp [Layout.time] at ht
    omega
  apply normalized_no_improvement hp hswap (p y)
  · intro j hj
    have hy : p.symm j ≠ y := by
      intro h
      have : j = p y := by simpa using congrArg p h
      exact (ne_of_lt hj) this
    have hx : p.symm j ≠ x := by
      intro h
      have : j = p x := by simpa using congrArg p h
      rw [this] at hj
      exact (not_lt_of_ge hpos.le) hj
    simp [Layout.exchange, Equiv.swap_apply_of_ne_of_ne hx hy]
  · simpa [Layout.exchange] using hbetter

end Structure
end ThreeMachine

namespace ThreeMachine.Structure

section Walk
variable {J : Type}

def PredAt (r : J → J → Prop) (time : J → ℕ) (s : ℕ) : Set J :=
  {x | ∃ y, time y = s ∧ r x y}

def DescAt (r : J → J → Prop) (time : J → ℕ) (s : ℕ) : Set J :=
  {x | ∃ y, time y = s ∧ r y x}

def IdealOn (W : Finset J) (r : J → J → Prop) (S : Set J) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, r x y → y ∈ S → x ∈ S

def PrefixOn (W : Finset J) (priority : J → ℕ) (S : Set J) : Prop :=
  ∀ x ∈ W, x ∈ S → ∀ y ∈ W, y ∉ S → priority x < priority y

def EarlierHigh (W : Finset J) (r : J → J → Prop) (time : J → ℕ)
    (S : Set J) (s : ℕ) : Prop :=
  ∀ x ∈ W, time x < s → x ∉ S → x ∈ PredAt r time s

def LaterLow (W : Finset J) (r : J → J → Prop) (time : J → ℕ)
    (S : Set J) (s : ℕ) : Prop :=
  ∀ x ∈ W, s < time x → x ∈ S → x ∈ DescAt r time s

def Separator (W : Finset J) (r : J → J → Prop) (time : J → ℕ)
    (S : Set J) (s : ℕ) : Prop :=
  EarlierHigh W r time S s ∧ LaterLow W r time S s

def SlotClosed (W : Finset J) (time : J → ℕ) : Prop :=
  ∀ x ∈ W, ∀ y, time y = time x → y ∈ W

def AdmissiblePosition (W : Finset J) (time : J → ℕ) (s : ℕ) : Prop :=
  (∃ x ∈ W, time x = s) ∨ (∀ x ∈ W, s < time x)

def LocalObstruction (W : Finset J) (r : J → J → Prop)
    (time priority : J → ℕ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, time y < time x → priority x < priority y →
    (∀ u ∈ W, r u x → time u < time y) →
    ∃ v ∈ W, r y v ∧ time v ≤ time x

theorem normalized_local_obstruction [Fintype J] {r : J → J → Prop} {priority : J → ℕ}
    {p : Layout J} (hp : p.Normalized r priority) :
    LocalObstruction Finset.univ r p.time priority := by
  classical
  intro x _ y _ ht hbetter hpred
  by_contra h
  have hsucc : ∀ v, r y v → p.time x < p.time v := by
    intro v hyv
    by_contra hn
    apply h
    exact ⟨v, Finset.mem_univ _, hyv, by omega⟩
  exact normalized_no_exchange hp x y ht hbetter
    (respects_exchange hp.1 x y ht (fun u hu => hpred u (Finset.mem_univ _) hu) hsucc)

structure Exception (W : Finset J) (r : J → J → Prop) (time : J → ℕ)
    (S : Set J) (s : ℕ) (x : J) : Prop where
  mem : x ∈ W
  low : x ∈ S
  later : s < time x
  not_desc : x ∉ DescAt r time s
  earliest : ∀ y ∈ W, y ∈ S → s < time y → time y < time x →
    y ∈ DescAt r time s

theorem exists_exception {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S : Set J} {s : ℕ} (h : ¬LaterLow W r time S s) :
    ∃ x, Exception W r time S s x := by
  classical
  let candidates := W.filter (fun x => s < time x ∧ x ∈ S ∧ x ∉ DescAt r time s)
  have hne : candidates.Nonempty := by
    simp only [LaterLow, not_forall] at h
    obtain ⟨x, hw, ht, hS, hD⟩ := h
    exact ⟨x, by simp [candidates, hw, ht, hS, hD]⟩
  obtain ⟨x, hx, hmin⟩ := candidates.exists_min_image time hne
  have hx' : x ∈ W ∧ s < time x ∧ x ∈ S ∧ x ∉ DescAt r time s := by
    simpa [candidates] using hx
  refine ⟨x, hx'.1, hx'.2.2.1, hx'.2.1, hx'.2.2.2, ?_⟩
  intro y hy hlow hsy hyx
  by_contra hnd
  have hmem : y ∈ candidates := by simp [candidates, hy, hsy, hlow, hnd]
  have := hmin y hmem
  omega

theorem exception_ready {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S : Set J} {s : ℕ} {x : J}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (hrespect : ∀ u v, r u v → time u < time v)
    (hideal : IdealOn W r S) (hx : Exception W r time S s x) :
    ∀ u ∈ W, r u x → time u < s := by
  intro u hu hux
  have huxTime := hrespect u x hux
  have huLow := hideal u hu x hx.mem hux hx.low
  by_contra hn
  have hsu : s ≤ time u := by omega
  rcases hsu.eq_or_lt with heq | hlt
  · exact hx.not_desc ⟨u, heq.symm, hux⟩
  · obtain ⟨y, hy, hyu⟩ := hx.earliest u hu huLow hlt huxTime
    exact hx.not_desc ⟨y, hy, htrans hyu hux⟩

theorem trace_to_slot {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S : Set J} {s t : ℕ}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (hrespect : ∀ u v, r u v → time u < time v)
    (hideal : IdealOn W r S)
    (hforce : ∀ y ∈ W, y ∉ S → s ≤ time y → time y < t →
      ∃ z ∈ W, r y z ∧ time z ≤ t)
    (y : J) (hy : y ∈ W) (hyHigh : y ∉ S) (hsy : s ≤ time y)
    (hyt : time y ≤ t) :
    ∃ z ∈ W, time z = t ∧ (y = z ∨ r y z) ∧ z ∉ S := by
  classical
  let candidates := W.filter (fun z => (y = z ∨ r y z) ∧ time z ≤ t)
  have hne : candidates.Nonempty := ⟨y, by simp [candidates, hy, hyt]⟩
  obtain ⟨z, hz, hmax⟩ := candidates.exists_max_image time hne
  have hz' : z ∈ W ∧ (y = z ∨ r y z) ∧ time z ≤ t := by
    simpa [candidates] using hz
  have hzHigh : z ∉ S := by
    intro hlow
    rcases hz'.2.1 with e | hrel
    · exact hyHigh (e ▸ hlow)
    · exact hyHigh (hideal y hy z hz'.1 hrel hlow)
  have hsz : s ≤ time z := by
    rcases hz'.2.1 with e | hrel
    · simpa [← e] using hsy
    · exact hsy.trans (hrespect y z hrel).le
  have hzt : time z = t := by
    by_contra hn
    have hlt : time z < t := by omega
    obtain ⟨v, hv, hzv, hvt⟩ := hforce z hz'.1 hzHigh hsz hlt
    have hyv : r y v := by
      rcases hz'.2.1 with e | hrel
      · simpa [e] using hzv
      · exact htrans hrel hzv
    have hv' : v ∈ candidates := by simp [candidates, hv, hyv, hvt]
    have := hmax v hv'
    have := hrespect z v hzv
    omega
  exact ⟨z, hz'.1, hzt, hz'.2.1, hzHigh⟩

theorem advance_earlier_high {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S : Set J} {s : ℕ} {x : J}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hideal : IdealOn W r S) (hprefix : PrefixOn W priority S)
    (hnorm : LocalObstruction W r time priority)
    (hbefore : EarlierHigh W r time S s) (hx : Exception W r time S s x) :
    EarlierHigh W r time S (time x) := by
  have hready := exception_ready htrans hrespect hideal hx
  have hforce : ∀ y ∈ W, y ∉ S → s ≤ time y → time y < time x →
      ∃ z ∈ W, r y z ∧ time z ≤ time x := by
    intro y hy hyHigh hsy hyt
    exact hnorm x hx.mem y hy hyt (hprefix x hx.mem hx.low y hy hyHigh)
      (fun u hu hur => (hready u hu hur).trans_le hsy)
  intro z hz hzt hzHigh
  by_cases hzs : time z < s
  · obtain ⟨y, hys, hzy⟩ := hbefore z hz hzs hzHigh
    have hy : y ∈ W := by
      rcases hpos with ⟨a, ha, has⟩ | hleft
      · exact hclosed a ha y (hys.trans has.symm)
      · have := hleft z hz
        omega
    have hyHigh : y ∉ S := by
      intro hylow
      exact hzHigh (hideal z hz y hy hzy hylow)
    obtain ⟨v, _hv, hvt, hyv, _hvHigh⟩ := trace_to_slot htrans hrespect hideal
      hforce y hy hyHigh (by omega) (by have := hx.later; omega)
    refine ⟨v, hvt, ?_⟩
    rcases hyv with e | hrel
    · simpa [e] using hzy
    · exact htrans hzy hrel
  · have hsz : s ≤ time z := by omega
    obtain ⟨v, _hv, hvt, hzv, _hvHigh⟩ := trace_to_slot htrans hrespect hideal
      hforce z hz hzHigh hsz hzt.le
    refine ⟨v, hvt, ?_⟩
    rcases hzv with e | hrel
    · subst v
      omega
    · exact hrel

theorem advance_shared_earlier {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S Splus : Set J} {s : ℕ} {x a : J}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hideal : IdealOn W r S) (hidealPlus : IdealOn W r Splus)
    (hprefix : PrefixOn W priority S) (hprefixPlus : PrefixOn W priority Splus)
    (hpromotion : ∀ z ∈ W, z ∈ Splus ↔ z ∈ S ∨ z = a)
    (hnorm : LocalObstruction W r time priority)
    (hbefore : EarlierHigh W r time S s)
    (hx : Exception W r time Splus s x) :
    EarlierHigh W r time S (time x) := by
  by_cases hxOld : x ∈ S
  · apply advance_earlier_high htrans hrespect hclosed hpos hideal hprefix hnorm hbefore
    exact ⟨hx.mem, hxOld, hx.later, hx.not_desc, fun y hy hlow hsy hyx =>
      hx.earliest y hy ((hpromotion y hy).mpr (Or.inl hlow)) hsy hyx⟩
  · have hxa : x = a := ((hpromotion x hx.mem).mp hx.low).resolve_left hxOld
    have hbeforePlus : EarlierHigh W r time Splus s := by
      intro z hz hzs hzHigh
      exact hbefore z hz hzs (fun h => hzHigh ((hpromotion z hz).mpr (Or.inl h)))
    have hnew := advance_earlier_high htrans hrespect hclosed hpos hidealPlus
      hprefixPlus hnorm hbeforePlus hx
    intro z hz hzx hzHigh
    apply hnew z hz hzx
    intro hlow
    rcases (hpromotion z hz).mp hlow with h | e
    · exact hzHigh h
    · have : z = x := e.trans hxa.symm
      have heq : time z = time x := congrArg time this
      omega

end Walk
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SharedWalk
variable {J : Type}

inductive AdvancePath (W : Finset J) (r : J → J → Prop) (time : J → ℕ)
    (S : Set J) : ℕ → ℕ → Prop
  | refl (s) : AdvancePath W r time S s s
  | step {s t x} : AdvancePath W r time S s t →
      Exception W r time S t x → AdvancePath W r time S s (time x)

theorem AdvancePath.le {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S : Set J} {s t : ℕ} (h : AdvancePath W r time S s t) : s ≤ t := by
  induction h with
  | refl => exact le_rfl
  | step _ hx ih => exact ih.trans hx.later.le

theorem AdvancePath.endpoint {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S : Set J} {s t : ℕ} (h : AdvancePath W r time S s t) :
    t = s ∨ ∃ x ∈ W, time x = t := by
  cases h with
  | refl => exact Or.inl rfl
  | step _ hx => exact Or.inr ⟨_, hx.mem, rfl⟩

theorem AdvancePath.admissible {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S : Set J} {s t : ℕ} (h : AdvancePath W r time S s t)
    (hpos : AdmissiblePosition W time s) : AdmissiblePosition W time t := by
  rcases h.endpoint with e | hmem
  · simpa [e] using hpos
  · exact Or.inl hmem

theorem AdvancePath.shared_earlier {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S Splus : Set J} {s t : ℕ} {a : J}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hideal : IdealOn W r S) (hidealPlus : IdealOn W r Splus)
    (hprefix : PrefixOn W priority S) (hprefixPlus : PrefixOn W priority Splus)
    (hpromotion : ∀ z ∈ W, z ∈ Splus ↔ z ∈ S ∨ z = a)
    (hnorm : LocalObstruction W r time priority)
    (hbefore : EarlierHigh W r time S s)
    (h : AdvancePath W r time Splus s t) : EarlierHigh W r time S t := by
  induction h with
  | refl => exact hbefore
  | step h hx ih =>
      exact advance_shared_earlier htrans hrespect hclosed (h.admissible hpos)
        hideal hidealPlus hprefix hprefixPlus hpromotion hnorm ih hx

theorem shared_cutoff {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S Splus : Set J} {s : ℕ} {a : J}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hideal : IdealOn W r S) (hidealPlus : IdealOn W r Splus)
    (hprefix : PrefixOn W priority S) (hprefixPlus : PrefixOn W priority Splus)
    (hpromotion : ∀ z ∈ W, z ∈ Splus ↔ z ∈ S ∨ z = a)
    (hnorm : LocalObstruction W r time priority)
    (hsep : Separator W r time S s) :
    ∃ t, s ≤ t ∧ AdvancePath W r time Splus s t ∧
      Separator W r time S t ∧ Separator W r time Splus t := by
  classical
  let candidates := (insert s (W.image time)).filter (AdvancePath W r time Splus s)
  have hne : candidates.Nonempty := ⟨s, by simp [candidates, AdvancePath.refl]⟩
  obtain ⟨t, ht, hmax⟩ := candidates.exists_max_image id hne
  have hpath : AdvancePath W r time Splus s t := (Finset.mem_filter.mp ht).2
  have hafter : LaterLow W r time Splus t := by
    by_contra hn
    obtain ⟨x, hx⟩ := exists_exception hn
    have hnext : AdvancePath W r time Splus s (time x) := .step hpath hx
    have hmem : time x ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_insert, Finset.mem_image]
      exact ⟨Or.inr ⟨x, hx.mem, rfl⟩, hnext⟩
    have := hmax (time x) hmem
    have := hx.later
    simp only [id_eq] at *
    omega
  have hbefore := hpath.shared_earlier htrans hrespect hclosed hpos hideal hidealPlus
    hprefix hprefixPlus hpromotion hnorm hsep.1
  refine ⟨t, hpath.le, hpath, ⟨hbefore, ?_⟩, ⟨?_, hafter⟩⟩
  · intro x hx htx hlow
    exact hafter x hx htx ((hpromotion x hx).mpr (Or.inl hlow))
  · intro x hx hxt hhigh
    exact hbefore x hx hxt (fun h => hhigh ((hpromotion x hx).mpr (Or.inl h)))

theorem separator_congr {W : Finset J} {r : J → J → Prop} {time : J → ℕ}
    {S Splus : Set J} {s : ℕ} (heq : ∀ z ∈ W, z ∈ S ↔ z ∈ Splus) :
    Separator W r time S s ↔ Separator W r time Splus s := by
  constructor
  · rintro ⟨hbefore, hafter⟩
    constructor
    · intro x hx hxt hhigh
      exact hbefore x hx hxt (fun h => hhigh ((heq x hx).mp h))
    · intro x hx htx hlow
      exact hafter x hx htx ((heq x hx).mpr hlow)
  · rintro ⟨hbefore, hafter⟩
    constructor
    · intro x hx hxt hhigh
      exact hbefore x hx hxt (fun h => hhigh ((heq x hx).mpr h))
    · intro x hx htx hlow
      exact hafter x hx htx ((heq x hx).mp hlow)

end SharedWalk
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section IdealSeparator
variable {J : Type}

theorem AdvancePath.earlier {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S : Set J} {s t : ℕ}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hideal : IdealOn W r S) (hprefix : PrefixOn W priority S)
    (hnorm : LocalObstruction W r time priority)
    (hbefore : EarlierHigh W r time S s)
    (h : AdvancePath W r time S s t) : EarlierHigh W r time S t := by
  induction h with
  | refl => exact hbefore
  | step h hx ih =>
      exact advance_earlier_high htrans hrespect hclosed
        (h.admissible hpos) hideal hprefix hnorm ih hx

theorem walk_to_separator {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {S : Set J} {s : ℕ}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hideal : IdealOn W r S) (hprefix : PrefixOn W priority S)
    (hnorm : LocalObstruction W r time priority)
    (hbefore : EarlierHigh W r time S s) :
    ∃ t, s ≤ t ∧ AdvancePath W r time S s t ∧ Separator W r time S t := by
  classical
  let candidates := (insert s (W.image time)).filter (AdvancePath W r time S s)
  have hne : candidates.Nonempty := ⟨s, by simp [candidates, AdvancePath.refl]⟩
  obtain ⟨t, ht, hmax⟩ := candidates.exists_max_image id hne
  have hpath : AdvancePath W r time S s t := (Finset.mem_filter.mp ht).2
  refine ⟨t, hpath.le, hpath, hpath.earlier htrans hrespect hclosed hpos hideal
    hprefix hnorm hbefore, ?_⟩
  by_contra hn
  obtain ⟨x, hx⟩ := exists_exception hn
  have hnext : AdvancePath W r time S s (time x) := .step hpath hx
  have hmem : time x ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_insert, Finset.mem_image]
    exact ⟨Or.inr ⟨x, hx.mem, rfl⟩, hnext⟩
  have := hmax (time x) hmem
  have := hx.later
  simp only [id_eq] at *
  omega

theorem ideal_has_separator [Fintype J] [Nonempty J]
    {r : J → J → Prop} {S : Set J} (p : Layout J) (hp : p.Full r)
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    (hideal : IdealOn Finset.univ r S) :
    ∃ q : Layout J, q.Full r ∧ ∃ t,
      (∃ x, q.time x = t) ∧ Separator Finset.univ r q.time S t := by
  classical
  let priority := fun x : J => if x ∈ S then (p x).val else Fintype.card J + (p x).val
  have hprefix : PrefixOn Finset.univ priority S := by
    intro x _ hx y _ hy
    simp only [priority, ite_eq_left hx, ite_eq_right hy]
    have := (p x).isLt
    omega
  obtain ⟨q, hq⟩ := exists_normalized r priority p hp.2
  have hcard : 0 < Fintype.card J := Fintype.card_pos
  let first := q.symm ⟨0, hcard⟩
  have hfirst : q.time first = 1 := by simp [Layout.time, first]
  have hbefore : EarlierHigh Finset.univ r q.time S 1 := by
    intro x _ hx _
    have : 1 ≤ q.time x := by simp [Layout.time]
    omega
  obtain ⟨t, _hst, hpath, hsep⟩ := walk_to_separator htrans hq.1
    (fun _ _ _ _ => Finset.mem_univ _) (Or.inl ⟨first, Finset.mem_univ _, hfirst⟩)
    hideal hprefix (normalized_local_obstruction hq) hbefore
  refine ⟨q, ⟨hp.1, hq.1⟩, t, ?_, hsep⟩
  rcases hpath.endpoint with e | ⟨x, _, hx⟩
  · exact ⟨first, hfirst.trans e.symm⟩
  · exact ⟨x, hx⟩

def BeforeTest (r : J → J → Prop) (time : J → ℕ) (s : ℕ) (H : Set J) : Set J :=
  PredAt r time s ∪ (H \ (DescAt r time s ∪ {x | time x = s}))

theorem separator_description {W : Finset J} {r : J → J → Prop}
    {time : J → ℕ} {s : ℕ} {S H : Set J}
    (hrespect : ∀ u v, r u v → time u < time v)
    (hsep : Separator W r time S s) (hagree : ∀ x ∈ W, x ∈ H ↔ x ∈ S) :
    ∀ x ∈ W, x ∈ BeforeTest r time s H ↔ time x < s := by
  intro x hx
  constructor
  · rintro (⟨y, hys, hxy⟩ | ⟨hH, hnd⟩)
    · have := hrespect x y hxy
      omega
    · have hS := (hagree x hx).mp hH
      have hne : time x ≠ s := fun he => hnd (Or.inr he)
      by_contra hn
      have hsx : s < time x := by omega
      exact hnd (Or.inl (hsep.2 x hx hsx hS))
  · intro hxs
    by_cases hS : x ∈ S
    · refine Or.inr ⟨(hagree x hx).mpr hS, ?_⟩
      rintro (⟨y, hys, hyx⟩ | he)
      · have := hrespect y x hyx
        omega
      · change time x = s at he
        omega
    · exact Or.inl (hsep.1 x hx hxs hS)

end IdealSeparator
end ThreeMachine.Structure

end

end OAI
