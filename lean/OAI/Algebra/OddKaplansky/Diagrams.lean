import OAI.Algebra.OddKaplansky.CoefficientOrder
import OAI.RingTheory.DirectFiniteness.ReducedWalks

namespace OAI

universe contextUniverse1 contextUniverse2

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7 portUniverse8 portUniverse9 portUniverse10 portUniverse11 portUniverse12 portUniverse13 portUniverse14 portUniverse15 portUniverse16 portUniverse17 portUniverse18 portUniverse19 portUniverse20 portUniverse21 portUniverse22 portUniverse23 portUniverse24 portUniverse25 portUniverse26 portUniverse27 portUniverse28 portUniverse29 portUniverse30 portUniverse31 portUniverse32 portUniverse33 portUniverse34 portUniverse35 portUniverse36 portUniverse37 portUniverse38 portUniverse39 portUniverse40 portUniverse41 portUniverse42 portUniverse43 portUniverse44 portUniverse45 portUniverse46 portUniverse47 portUniverse48 portUniverse49 portUniverse50 portUniverse51 portUniverse52 portUniverse53 portUniverse54 portUniverse55 portUniverse56 portUniverse57 portUniverse58 portUniverse59 portUniverse60 portUniverse61 portUniverse62 portUniverse63 portUniverse64 portUniverse65 portUniverse66 portUniverse67 portUniverse68 portUniverse69 portUniverse70 portUniverse71 portUniverse72 portUniverse73 portUniverse74 portUniverse75 portUniverse76

section

noncomputable section
open scoped Classical

noncomputable section
open scoped Classical BigOperators
open Equiv Equiv.Perm
namespace OddKaplansky.Planar
attribute [local simp] SameCycle.rfl

variable {α : Type portUniverse1} [Fintype α]

abbrev Cycles (p : Perm α) := Quotient (SameCycle.setoid p)

def cycleClass (p : Perm α) (x : α) : Cycles p := Quotient.mk _ x

def cycleSet (p : Perm α) (c : Cycles p) : Finset α :=
  Finset.univ.filter fun x => cycleClass p x = c

lemma mem_cycleSet (p : Perm α) (c : Cycles p) (x : α) :
    x ∈ cycleSet p c ↔ cycleClass p x = c := by simp [cycleSet]

omit [Fintype α] in
lemma cycleClass_eq (p : Perm α) (x y : α) :
    cycleClass p x = cycleClass p y ↔ p.SameCycle x y := Quotient.eq

lemma cycleSet_nonempty (p : Perm α) (c : Cycles p) : (cycleSet p c).Nonempty := by
  induction c using Quotient.inductionOn with
  | h x => exact ⟨x, (mem_cycleSet p _ x).mpr rfl⟩

lemma cycles_sum_card (p : Perm α) :
    ∑ c : Cycles p, (cycleSet p c).card = Fintype.card α := by
  classical
  simpa [cycleSet] using Finset.sum_card_fiberwise_eq_card_filter
    (s := Finset.univ) (t := Finset.univ) (g := cycleClass p)

structure Ribbon (α : Type portUniverse2) where
  black : Perm α
  white : Perm α

def Ribbon.face (R : Ribbon α) : Perm α := R.white * R.black

def Ribbon.Spherical (R : Ribbon α) : Prop :=
  Nat.card (Cycles R.black) + Nat.card (Cycles R.white) +
    Nat.card (Cycles R.face) = Fintype.card α + 2

def Ribbon.mergeWhite (R : Ribbon α) (e : α) : Ribbon α where
  black := R.black
  white := swap e (R.face e) * R.white

omit [Fintype α] in
lemma mergeWhite_face (R : Ribbon α) (e : α) :
    (R.mergeWhite e).face = swap e (R.face e) * R.face := by
  simp [Ribbon.mergeWhite, Ribbon.face, mul_assoc]

omit [Fintype α] in
lemma mergeWhite_face_fixed (R : Ribbon α) (e : α) : (R.mergeWhite e).face e = e := by
  rw [mergeWhite_face]
  simp

lemma sameCycle_map {β : Type portUniverse3} (p : Perm α) (q : Perm β) (f : α → β)
    (hstep : ∀ x, q.SameCycle (f x) (f (p x))) {x y : α}
    (hxy : p.SameCycle x y) : q.SameCycle (f x) (f y) := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (hstep _)

def unplug (p : Perm α) (a : α) : Perm α := swap a (p a) * p

def bypass (p : Perm α) (a x : α) : α := if x = a then p a else x

omit [Fintype α] in
lemma unplug_fixed (p : Perm α) (a : α) : unplug p a a = a := by
  simp [unplug]

lemma unplug_sameCycle (p : Perm α) (a : α) {x y : α}
    (h : (unplug p a).SameCycle x y) : p.SameCycle x y := by
  apply sameCycle_map (unplug p a) p id _ h
  intro x
  change p.SameCycle x (swap a (p a) (p x))
  by_cases hx : x = a
  · subst x
    simp
  · by_cases hxa : p x = a
    · simp only [hxa, swap_apply_left]
      exact (show p.SameCycle x a by rw [← hxa]; simp).trans (by simp)
    · have hxp : p x ≠ p a := p.injective.ne hx
      rw [swap_apply_of_ne_of_ne hxa hxp]
      simp

lemma sameCycle_bypass (p : Perm α) (a : α) (ha : p a ≠ a) {x y : α}
    (h : p.SameCycle x y) :
    (unplug p a).SameCycle (bypass p a x) (bypass p a y) := by
  apply sameCycle_map p (unplug p a) (bypass p a) _ h
  intro x
  by_cases hx : x = a
  · subst x
    simp [bypass, ha]
  · by_cases hxa : p x = a
    · have hq : unplug p a x = p a := by simp [unplug, hxa]
      simp only [bypass, hx, hxa, ite_false, ite_true]
      rw [← hq]
      simp
    · have hxp : p x ≠ p a := p.injective.ne hx
      have hq : unplug p a x = p x := by
        simp only [unplug, Perm.mul_apply]
        exact swap_apply_of_ne_of_ne hxa hxp
      simp only [bypass, hx, hxa, ite_false]
      rw [← hq]
      simp

lemma unplug_sameCycle_iff (p : Perm α) (a : α) (ha : p a ≠ a)
    {x y : α} (hx : x ≠ a) (hy : y ≠ a) :
    (unplug p a).SameCycle x y ↔ p.SameCycle x y := by
  refine ⟨unplug_sameCycle p a, fun h => ?_⟩
  simpa [bypass, hx, hy] using sameCycle_bypass p a ha h

omit [Fintype α] in
lemma bypass_ne (p : Perm α) (a : α) (ha : p a ≠ a) (x : α) :
    bypass p a x ≠ a := by
  by_cases hx : x = a <;> simp [bypass, hx, ha]

def unplugCycleEquiv (p : Perm α) (a : α) (ha : p a ≠ a) :
    Cycles p ≃ {c : Cycles (unplug p a) // c ≠ cycleClass (unplug p a) a} where
  toFun := Quotient.lift (fun x =>
    ⟨cycleClass (unplug p a) (bypass p a x), by
      intro h
      have he := (cycleClass_eq _ _ _).mp h
      exact bypass_ne p a ha x (he.eq_of_right (unplug_fixed p a))⟩)
    (fun x y h => Subtype.ext ((cycleClass_eq _ _ _).mpr (sameCycle_bypass p a ha h)))
  invFun c := Quotient.map' id (fun _ _ h => unplug_sameCycle p a h) c.val
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change cycleClass p (bypass p a x) = cycleClass p x
      apply (cycleClass_eq _ _ _).mpr
      by_cases hx : x = a <;> simp [bypass, hx]
  right_inv c := by
    rcases c with ⟨c, hc⟩
    apply Subtype.ext
    induction c using Quotient.inductionOn with
    | h x =>
      have hx : x ≠ a := by
        intro h
        apply hc
        exact congrArg (cycleClass _) h
      change cycleClass (unplug p a) (bypass p a x) = cycleClass (unplug p a) x
      simp [bypass, hx]

lemma unplug_cycles_card (p : Perm α) (a : α) (ha : p a ≠ a) :
    Nat.card (Cycles (unplug p a)) = Nat.card (Cycles p) + 1 := by
  have h := Fintype.card_congr (unplugCycleEquiv p a ha)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h
  have hp : 0 < Fintype.card (Cycles (unplug p a)) :=
    Fintype.card_pos_iff.mpr ⟨cycleClass (unplug p a) a⟩
  simp only [Nat.card_eq_fintype_card]
  omega

lemma swap_mul_sameCycle (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) :
    (swap a b * p).SameCycle a b := by
  have hret : ∃ n : ℕ, 0 < n ∧ (p ^ n) b = b := by
    exact ⟨orderOf p, orderOf_pos p, by simp⟩
  let n := Nat.find hret
  have hn : 0 < n ∧ (p ^ n) b = b := Nat.find_spec hret
  have hmin : ∀ k, 0 < k → k < n → (p ^ k) b ≠ b := by
    intro k hk hkn heq
    exact Nat.find_min hret hkn ⟨hk, heq⟩
  have hneq : ∀ k : ℕ, (p ^ k) b ≠ a := by
    intro k heq
    apply hab
    exact (show p.SameCycle b a from ⟨k, by simpa using heq⟩).symm
  have hiter : ∀ k, k < n → ((swap a b * p) ^ k) b = (p ^ k) b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      rw [pow_succ', Perm.mul_apply, ih (by omega), Perm.mul_apply]
      have heq : p ((p ^ k) b) = (p ^ (k + 1)) b := by
        rw [pow_succ', Perm.mul_apply]
      rw [heq, swap_apply_of_ne_of_ne (hneq _) (hmin _ (by omega) hk)]
  have hn' : n - 1 + 1 = n := by omega
  have hstep : ((swap a b * p) ^ n) b = a := by
    rw [← hn', pow_succ', Perm.mul_apply, hiter _ (by omega), Perm.mul_apply]
    have heq : p ((p ^ (n - 1)) b) = b := by
      calc
        p ((p ^ (n - 1)) b) = (p ^ (n - 1 + 1)) b := by rw [pow_succ', Perm.mul_apply]
        _ = b := by rw [hn']; exact hn.2
    rw [heq, swap_apply_right]
  exact (show (swap a b * p).SameCycle b a from ⟨n, by simpa using hstep⟩).symm

lemma sameCycle_swap_mul (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b)
    {x y : α} (hxy : p.SameCycle x y) : (swap a b * p).SameCycle x y := by
  have hlink := swap_mul_sameCycle p a b hab
  apply sameCycle_map p (swap a b * p) id _ hxy
  intro x
  have hx : (swap a b * p).SameCycle x (swap a b (p x)) := by
    change (swap a b * p).SameCycle x ((swap a b * p) x)
    exact SameCycle.apply_right SameCycle.rfl
  by_cases hxa : p x = a
  · rw [hxa, swap_apply_left] at hx
    exact hx.trans (hxa ▸ hlink.symm)
  · by_cases hxb : p x = b
    · rw [hxb, swap_apply_right] at hx
      exact hx.trans (hxb ▸ hlink)
    · rwa [swap_apply_of_ne_of_ne hxa hxb] at hx

def mergedClass (p : Perm α) (a b : α) (x : α) : Cycles p :=
  if cycleClass p x = cycleClass p b then cycleClass p a else cycleClass p x

omit [Fintype α] in
lemma cycleClass_apply (p : Perm α) (x : α) : cycleClass p (p x) = cycleClass p x := by
  apply (cycleClass_eq _ _ _).mpr
  exact SameCycle.apply_left SameCycle.rfl

omit [Fintype α] in
lemma mergedClass_step (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) (x : α) :
    mergedClass p a b ((swap a b * p) x) = mergedClass p a b x := by
  have hne : cycleClass p a ≠ cycleClass p b := mt (cycleClass_eq p a b).mp hab
  change mergedClass p a b (swap a b (p x)) = _
  by_cases hxa : p x = a
  · have hx : cycleClass p x = cycleClass p a := by
      rw [← cycleClass_apply, hxa]
    simp [mergedClass, hxa, hx, hne]
  · by_cases hxb : p x = b
    · have hx : cycleClass p x = cycleClass p b := by
        rw [← cycleClass_apply, hxb]
      simp [mergedClass, hxb, hx, hne]
    · simp [swap_apply_of_ne_of_ne hxa hxb, mergedClass, cycleClass_apply]

lemma mergedClass_cycle (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b)
    {x y : α} (hxy : (swap a b * p).SameCycle x y) :
    mergedClass p a b x = mergedClass p a b y := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, mergedClass_step p a b hab]
    exact ih

def mergeCycleEquiv (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) :
    Cycles (swap a b * p) ≃ {c : Cycles p // c ≠ cycleClass p b} where
  toFun := Quotient.lift (fun x => ⟨mergedClass p a b x, by
    have hne : cycleClass p a ≠ cycleClass p b := mt (cycleClass_eq p a b).mp hab
    simp only [mergedClass]
    split_ifs with h <;> assumption⟩)
    (fun _ _ h => Subtype.ext (mergedClass_cycle p a b hab h))
  invFun c := Quotient.map' id (fun _ _ h => sameCycle_swap_mul p a b hab h) c.val
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change Quotient.map' id _ (mergedClass p a b x) = cycleClass (swap a b * p) x
      unfold mergedClass
      split_ifs with hx
      · apply (cycleClass_eq _ _ _).mpr
        exact (swap_mul_sameCycle p a b hab).trans
          (sameCycle_swap_mul p a b hab ((cycleClass_eq _ _ _).mp hx).symm)
      · rfl
  right_inv c := by
    apply Subtype.ext
    rcases c with ⟨c, hc⟩
    induction c using Quotient.inductionOn with
    | h x =>
      change mergedClass p a b x = cycleClass p x
      change cycleClass p x ≠ cycleClass p b at hc
      simp [mergedClass, hc]

lemma swap_mul_cycles_card (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) :
    Nat.card (Cycles (swap a b * p)) + 1 = Nat.card (Cycles p) := by
  have h := Fintype.card_congr (mergeCycleEquiv p a b hab)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h
  have hp : 0 < Fintype.card (Cycles p) := Fintype.card_pos_iff.mpr ⟨cycleClass p a⟩
  simp only [Nat.card_eq_fintype_card]
  omega

lemma mergeWhite_spherical (R : Ribbon α) (hR : R.Spherical) (e : α)
    (he : ¬ R.white.SameCycle e (R.black e)) : (R.mergeWhite e).Spherical := by
  have hn : ¬ R.white.SameCycle e (R.face e) := by
    simpa [Ribbon.face] using he
  have hne : R.face e ≠ e := by
    intro h
    apply hn
    rw [h]
  have hw := swap_mul_cycles_card R.white e (R.face e) hn
  have hf := unplug_cycles_card R.face e hne
  unfold Ribbon.Spherical at *
  change Nat.card (Cycles R.black) +
    Nat.card (Cycles (swap e (R.face e) * R.white)) + _ = _
  rw [mergeWhite_face]
  change Nat.card (Cycles R.black) +
    Nat.card (Cycles (swap e (R.face e) * R.white)) +
    Nat.card (Cycles (unplug R.face e)) = Fintype.card α + 2
  omega

theorem euler_contradiction (R : Ribbon α) (hR : R.Spherical)
    (w : Cycles R.white) (f : Cycles R.face)
    (hb : ∀ c : Cycles R.black, 3 ≤ (cycleSet R.black c).card)
    (hw : ∀ c : Cycles R.white, 2 ≤ (cycleSet R.white c).card + if c = w then 1 else 0)
    (hf : ∀ c : Cycles R.face, 6 ≤ (cycleSet R.face c).card + if c = f then 6 else 0) :
    False := by
  have hb' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.black))) => hb c)
  have hw' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.white))) => hw c)
  have hf' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.face))) => hf c)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, cycles_sum_card] at hb'
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.sum_add_distrib,
    cycles_sum_card, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hw' hf'
  unfold Ribbon.Spherical at hR
  simp only [Nat.card_eq_fintype_card] at hR
  omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
variable {α : Type portUniverse4} [Fintype α]

lemma sameCycle_map_quotient {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) :
    Nat.card (Cycles q) ≤ Nat.card (Cycles p) := by
  exact Nat.card_le_card_of_surjective (Quotient.map id (fun _ _ hxy => h hxy))
    (Quotient.map_surjective _ Function.surjective_id)

lemma swap_cycles_card_le (p : Perm α) (a b : α) :
    Nat.card (Cycles (swap a b * p)) ≤ Nat.card (Cycles p) + 1 := by
  let q := swap a b * p
  have hrev : swap a b * q = p := by simp [q, ← mul_assoc]
  by_cases hab : q.SameCycle a b
  · have href : ∀ {x y}, p.SameCycle x y → q.SameCycle x y := by
      intro x y h
      apply sameCycle_map p q id _ h
      intro x
      have hx : q.SameCycle x (q x) := by simp
      have hp : p x = swap a b (q x) := by
        rw [← Perm.mul_apply, hrev]
      rw [hp]
      by_cases hxa : q x = a
      · rw [hxa] at hx
        simpa [hxa] using hx.trans hab
      · by_cases hxb : q x = b
        · rw [hxb] at hx
          simpa [hxb] using hx.trans hab.symm
        · rwa [swap_apply_of_ne_of_ne hxa hxb]
    exact (sameCycle_map_quotient href).trans (Nat.le_succ _)
  · have h := swap_mul_cycles_card q a b hab
    rw [hrev] at h
    change Nat.card (Cycles q) ≤ _
    omega

lemma cycles_card_le (p : Perm α) : Nat.card (Cycles p) ≤ Fintype.card α := by
  simpa using Nat.card_le_card_of_surjective (cycleClass p) Quotient.mk_surjective

lemma cycles_one_card : Nat.card (Cycles (1 : Perm α)) = Fintype.card α := by
  have heq : SameCycle.setoid (1 : Perm α) = ⊥ := by
    ext x y
    exact sameCycle_one
  rw [Cycles, heq]
  exact (Nat.card_congr Setoid.quotientBotEquiv).trans (Nat.card_eq_fintype_card)

lemma exists_cycle_factorization (p : Perm α) :
    ∃ l : List (α × α),
      (l.map fun ab => swap ab.1 ab.2).prod = p ∧
      l.length + Nat.card (Cycles p) = Fintype.card α ∧
      ∀ ab ∈ l, ab.1 ≠ ab.2 ∧ p.SameCycle ab.1 ab.2 := by
  have hmain : ∀ n : ℕ, ∀ p : Perm α,
      Fintype.card α - Nat.card (Cycles p) = n →
      ∃ l : List (α × α),
        (l.map fun ab => swap ab.1 ab.2).prod = p ∧
        l.length + Nat.card (Cycles p) = Fintype.card α ∧
        ∀ ab ∈ l, ab.1 ≠ ab.2 ∧ p.SameCycle ab.1 ab.2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      by_cases hp : p = 1
      · subst p
        exact ⟨[], by simp, by simpa using cycles_one_card (α := α), by simp⟩
      · have hex : ∃ a, p a ≠ a := by
          by_contra! h
          exact hp (Equiv.ext h)
        obtain ⟨a, ha⟩ := hex
        have hc := unplug_cycles_card p a ha
        have hle := cycles_card_le (unplug p a)
        have hlt : Fintype.card α - Nat.card (Cycles (unplug p a)) < n := by omega
        obtain ⟨l, hl, hlen, hmem⟩ := ih _ hlt (unplug p a) rfl
        refine ⟨(a, p a) :: l, ?_, ?_, ?_⟩
        · simp only [List.map_cons, List.prod_cons, hl]
          simp [unplug, ← mul_assoc]
        · simp only [List.length_cons]
          omega
        · intro ab hab
          rcases List.mem_cons.mp hab with rfl | hab
          · exact ⟨Ne.symm ha, by simp⟩
          · exact ⟨(hmem ab hab).1, unplug_sameCycle p a (hmem ab hab).2⟩
  exact hmain _ p rfl

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse5}

def mergeClass (s : Setoid α) (a b x : α) : Quotient s :=
  if Quotient.mk s x = Quotient.mk s b then Quotient.mk s a else Quotient.mk s x

def joinPair (s : Setoid α) (a b : α) : Setoid α := Setoid.ker (mergeClass s a b)

lemma le_joinPair (s : Setoid α) (a b : α) : s ≤ joinPair s a b := by
  intro x y hxy
  change mergeClass s a b x = mergeClass s a b y
  simp only [mergeClass, Quotient.sound hxy]

lemma joinPair_related (s : Setoid α) (a b : α) : (joinPair s a b).r a b := by
  change mergeClass s a b a = mergeClass s a b b
  simp [mergeClass]

lemma joinPair_eq_of_related (s : Setoid α) {a b : α} (hab : s.r a b) :
    joinPair s a b = s := by
  ext x y
  have h : ∀ x, mergeClass s a b x = Quotient.mk s x := by
    intro x
    simp only [mergeClass, ← Quotient.sound hab]
    split_ifs with hx
    · exact hx.symm
    · rfl
  change mergeClass s a b x = mergeClass s a b y ↔ s.r x y
  rw [h, h, Quotient.eq]

lemma joinPair_le (s t : Setoid α) (a b : α) (hst : s ≤ t) (hab : t.r a b) :
    joinPair s a b ≤ t := by
  intro x y hxy
  change mergeClass s a b x = mergeClass s a b y at hxy
  by_cases hx : Quotient.mk s x = Quotient.mk s b
  · by_cases hy : Quotient.mk s y = Quotient.mk s b
    · exact t.iseqv.trans (hst (Quotient.exact hx)) (t.iseqv.symm (hst (Quotient.exact hy)))
    · simp only [mergeClass, hx, hy, ite_true, ite_false] at hxy
      exact t.iseqv.trans (t.iseqv.trans (hst (Quotient.exact hx)) (t.iseqv.symm hab)) (hst (Quotient.exact hxy))
  · by_cases hy : Quotient.mk s y = Quotient.mk s b
    · simp only [mergeClass, hx, hy, ite_true, ite_false] at hxy
      exact t.iseqv.trans (t.iseqv.trans (hst (Quotient.exact hxy)) hab) (t.iseqv.symm (hst (Quotient.exact hy)))
    · simp only [mergeClass, hx, hy, ite_false] at hxy
      exact hst (Quotient.exact hxy)

def joinPairEquiv (s : Setoid α) (a b : α) (hab : ¬ s.r a b) :
    Quotient (joinPair s a b) ≃ {c : Quotient s // c ≠ Quotient.mk s b} where
  toFun := Quotient.lift (fun x => ⟨mergeClass s a b x, by
    have hne : Quotient.mk s a ≠ Quotient.mk s b := fun h => hab (Quotient.exact h)
    simp only [mergeClass]
    split_ifs with hx <;> assumption⟩) (fun _ _ h => Subtype.ext h)
  invFun c := Quotient.map id (fun _ _ h => le_joinPair s a b h) c.val
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change Quotient.map id _ (mergeClass s a b x) = Quotient.mk _ x
      unfold mergeClass
      split_ifs with hx
      · apply Quotient.sound
        exact (joinPair s a b).iseqv.trans (joinPair_related s a b) (le_joinPair s a b (s.iseqv.symm (Quotient.exact hx)))
      · rfl
  right_inv c := by
    rcases c with ⟨c, hc⟩
    apply Subtype.ext
    induction c using Quotient.inductionOn with
    | h x =>
      change mergeClass s a b x = Quotient.mk s x
      simp [mergeClass, hc]

lemma joinPair_card [Fintype α] (s : Setoid α) (a b : α) (hab : ¬ s.r a b) :
    Nat.card (Quotient (joinPair s a b)) + 1 = Nat.card (Quotient s) := by
  have h := Fintype.card_congr (joinPairEquiv s a b hab)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h
  have hp : 0 < Fintype.card (Quotient s) := Fintype.card_pos_iff.mpr ⟨Quotient.mk s a⟩
  simp only [Nat.card_eq_fintype_card]
  omega

lemma setoid_swap_related (s : Setoid α) {a b : α} (hab : s.r a b) (x : α) :
    s.r x (swap a b x) := by
  by_cases ha : x = a
  · subst x
    simpa using hab
  · by_cases hb : x = b
    · subst x
      simpa using s.iseqv.symm hab
    · rw [swap_apply_of_ne_of_ne ha hb]

lemma setoid_sameCycle_of_step [Fintype α] (s : Setoid α) (p : Perm α)
    (hstep : ∀ x, s.r x (p x)) {x y : α} (hxy : p.SameCycle x y) : s.r x y := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact s.iseqv.refl _
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact s.iseqv.trans ih (hstep _)

def edgePartition : List (α × α) → Setoid α
  | [] => ⊥
  | (a, b) :: l => joinPair (edgePartition l) a b

lemma edgePartition_le {l : List (α × α)} {s : Setoid α}
    (h : ∀ ab ∈ l, s.r ab.1 ab.2) : edgePartition l ≤ s := by
  induction l with
  | nil => exact bot_le
  | cons ab l ih =>
    exact joinPair_le _ _ _ _ (ih fun ab hab => h ab (List.mem_cons_of_mem _ hab))
      (h ab List.mem_cons_self)

lemma edgePartition_pair {l : List (α × α)} {ab : α × α} (h : ab ∈ l) :
    (edgePartition l).r ab.1 ab.2 := by
  induction l with
  | nil => simp at h
  | cons cd l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact joinPair_related _ _ _
    · exact le_joinPair _ _ _ (ih h)

lemma edgePartition_prod (l : List (α × α)) (x : α) :
    (edgePartition l).r x ((l.map fun ab => swap ab.1 ab.2).prod x) := by
  induction l with
  | nil => exact (⊥ : Setoid α).iseqv.refl x
  | cons ab l ih =>
    simp only [List.map_cons, List.prod_cons, Perm.mul_apply]
    exact (edgePartition (ab :: l)).iseqv.trans (le_joinPair _ _ _ ih)
      (setoid_swap_related (edgePartition (ab :: l)) (joinPair_related _ _ _) _)

lemma transposition_euler_bound [Fintype α] (l : List (α × α)) :
    Fintype.card α + Nat.card (Cycles (l.map fun ab => swap ab.1 ab.2).prod) ≤
      l.length + 2 * Nat.card (Quotient (edgePartition l)) := by
  induction l with
  | nil =>
    change Fintype.card α + Nat.card (Cycles (1 : Perm α)) ≤
      0 + 2 * Nat.card (Quotient (⊥ : Setoid α))
    rw [cycles_one_card, Nat.card_congr Setoid.quotientBotEquiv, Nat.card_eq_fintype_card]
    omega
  | cons ab l ih =>
    let p := (l.map fun ab => swap ab.1 ab.2).prod
    change Fintype.card α + Nat.card (Cycles (swap ab.1 ab.2 * p)) ≤
      (l.length + 1) + 2 * Nat.card (Quotient (joinPair (edgePartition l) ab.1 ab.2))
    by_cases h : (edgePartition l).r ab.1 ab.2
    · rw [joinPair_eq_of_related _ h]
      have hc := swap_cycles_card_le p ab.1 ab.2
      change Fintype.card α + Nat.card (Cycles p) ≤ _ at ih
      omega
    · have hab : ¬ p.SameCycle ab.1 ab.2 := by
        intro hc
        exact h (setoid_sameCycle_of_step (edgePartition l) p (edgePartition_prod l) hc)
      have hc := swap_mul_cycles_card p ab.1 ab.2 hab
      have hs := joinPair_card (edgePartition l) ab.1 ab.2 h
      change Fintype.card α + Nat.card (Cycles p) ≤ _ at ih
      omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse6} [Fintype α]

lemma quotient_card_antitone {s t : Setoid α} (h : s ≤ t) :
    Nat.card (Quotient t) ≤ Nat.card (Quotient s) := by
  exact Nat.card_le_card_of_surjective (Quotient.map id (fun _ _ hxy => h hxy))
    (Quotient.map_surjective _ Function.surjective_id)

def Ribbon.components (R : Ribbon α) : Setoid α :=
  SameCycle.setoid R.black ⊔ SameCycle.setoid R.white

omit [Fintype α] in
lemma cycles_inv_card (p : Perm α) : Nat.card (Cycles p⁻¹) = Nat.card (Cycles p) := by
  have h : SameCycle.setoid p⁻¹ = SameCycle.setoid p := by
    ext a b
    exact sameCycle_inv
  unfold Cycles
  rw [h]

theorem Ribbon.euler_le (R : Ribbon α) :
    Nat.card (Cycles R.black) + Nat.card (Cycles R.white) + Nat.card (Cycles R.face) ≤
      Fintype.card α + 2 * Nat.card (Quotient R.components) := by
  obtain ⟨lb, hb, hblen, _⟩ := exists_cycle_factorization R.black
  obtain ⟨lw, hw, hwlen, _⟩ := exists_cycle_factorization R.white
  obtain ⟨lf, hf, hflen, _⟩ := exists_cycle_factorization R.face⁻¹
  rw [cycles_inv_card] at hflen
  let l := lw ++ lb ++ lf
  have hl : (l.map fun ab => swap ab.1 ab.2).prod = 1 := by
    simp only [l, List.map_append, List.prod_append, hb, hw, hf]
    change R.face * R.face⁻¹ = 1
    exact mul_inv_cancel _
  have hbl : edgePartition lb ≤ edgePartition l := by
    apply edgePartition_le
    intro ab hab
    apply edgePartition_pair
    simp [l, hab]
  have hwl : edgePartition lw ≤ edgePartition l := by
    apply edgePartition_le
    intro ab hab
    apply edgePartition_pair
    simp [l, hab]
  have hcomp : R.components ≤ edgePartition l := by
    apply sup_le
    · intro x y hxy
      apply setoid_sameCycle_of_step (edgePartition l) R.black _ hxy
      intro x
      rw [← hb]
      exact hbl (edgePartition_prod lb x)
    · intro x y hxy
      apply setoid_sameCycle_of_step (edgePartition l) R.white _ hxy
      intro x
      rw [← hw]
      exact hwl (edgePartition_prod lw x)
  have hc := quotient_card_antitone hcomp
  have hbound := transposition_euler_bound l
  rw [hl, cycles_one_card] at hbound
  have hlen : l.length = lw.length + lb.length + lf.length := by simp [l, Nat.add_assoc]
  omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse7}

def restrictQuotient (s : Setoid α) (P : α → Prop) :
    Quotient (s.comap (Subtype.val : {x // P x} → α)) → Quotient s :=
  Quotient.map Subtype.val (fun _ _ h => h)

lemma restrictQuotient_injective (s : Setoid α) (P : α → Prop) :
    Function.Injective (restrictQuotient s P) := by
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | h x y =>
    intro h
    change Quotient.mk s x.val = Quotient.mk s y.val at h
    apply Quotient.sound
    change s.r x.val y.val
    exact Quotient.exact h

def quotientRestrictSumEquiv (s : Setoid α) (P : α → Prop)
    (hP : ∀ {x y}, s.r x y → (P x ↔ P y)) :
    (Quotient (s.comap (Subtype.val : {x // P x} → α)) ⊕
      Quotient (s.comap (Subtype.val : {x // ¬ P x} → α))) ≃ Quotient s :=
  Equiv.ofBijective (Sum.elim (restrictQuotient s P) (restrictQuotient s (fun x => ¬ P x))) (by
    constructor
    · intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (restrictQuotient_injective s P hab)
        | inr b =>
          induction a, b using Quotient.inductionOn₂ with
          | h a b => exact (b.prop ((hP (Quotient.exact hab)).mp a.prop)).elim
      | inr a =>
        cases b with
        | inl b =>
          induction a, b using Quotient.inductionOn₂ with
          | h a b => exact (a.prop ((hP (Quotient.exact hab)).mpr b.prop)).elim
        | inr b => exact congrArg Sum.inr (restrictQuotient_injective s _ hab)
    · intro c
      induction c using Quotient.inductionOn with
      | h x =>
        by_cases hx : P x
        · exact ⟨Sum.inl (Quotient.mk _ ⟨x, hx⟩), rfl⟩
        · exact ⟨Sum.inr (Quotient.mk _ ⟨x, hx⟩), rfl⟩)

lemma quotient_restrict_card_split [Fintype α] (s : Setoid α) (P : α → Prop)
    (hP : ∀ {x y}, s.r x y → (P x ↔ P y)) :
    Nat.card (Quotient (s.comap (Subtype.val : {x // P x} → α))) +
      Nat.card (Quotient (s.comap (Subtype.val : {x // ¬ P x} → α))) =
      Nat.card (Quotient s) := by
  simpa only [Nat.card_sum] using Nat.card_congr (quotientRestrictSumEquiv s P hP)

variable [Fintype α]

lemma perm_invariant_cycle (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x)
    {x y : α} (hxy : p.SameCycle x y) : P x ↔ P y := by
  exact Iff.of_eq (setoid_sameCycle_of_step (Setoid.ker P) p
    (fun x => propext (hP x).symm) hxy)

omit [Fintype α] in
lemma subtype_cycles_setoid (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    SameCycle.setoid (p.subtypePerm hP) =
      (SameCycle.setoid p).comap (Subtype.val : {x // P x} → α) := by
  ext x y
  exact sameCycle_subtypePerm

lemma cycles_restrict_card_split (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    Nat.card (Cycles (p.subtypePerm hP)) +
      Nat.card (Cycles (p.subtypePerm (p := fun x => ¬ P x) fun x => not_congr (hP x))) = Nat.card (Cycles p) := by
  unfold Cycles
  rw [subtype_cycles_setoid, subtype_cycles_setoid]
  exact quotient_restrict_card_split _ P (perm_invariant_cycle p P hP)

def Ribbon.restrict (R : Ribbon α) (P : α → Prop)
    (hb : ∀ x, P (R.black x) ↔ P x) (hw : ∀ x, P (R.white x) ↔ P x) :
    Ribbon {x // P x} where
  black := R.black.subtypePerm hb
  white := R.white.subtypePerm hw

omit [Fintype α] in
lemma Ribbon.restrict_face (R : Ribbon α) (P : α → Prop) (hb hw) :
    (R.restrict P hb hw).face = R.face.subtypePerm (fun x => (hw _).trans (hb x)) := rfl

lemma Ribbon.invariant_components (R : Ribbon α) (P : α → Prop)
    (hb : ∀ x, P (R.black x) ↔ P x) (hw : ∀ x, P (R.white x) ↔ P x)
    {x y : α} (hxy : R.components.r x y) : P x ↔ P y := by
  have h : R.components ≤ Setoid.ker P := by
    apply sup_le
    · exact fun _ _ h => propext (perm_invariant_cycle R.black P hb h)
    · exact fun _ _ h => propext (perm_invariant_cycle R.white P hw h)
  exact Iff.of_eq (h hxy)

lemma Ribbon.restrict_components (R : Ribbon α) (P : α → Prop) (hb hw) :
    (R.restrict P hb hw).components =
      R.components.comap (Subtype.val : {x // P x} → α) := by
  apply le_antisymm
  · apply sup_le
    · intro x y h
      exact (show SameCycle.setoid R.black ≤ R.components from le_sup_left) ((sameCycle_subtypePerm (h := hb)).mp h)
    · intro x y h
      exact (show SameCycle.setoid R.white ≤ R.components from le_sup_right) ((sameCycle_subtypePerm (h := hw)).mp h)
  · intro x y hxy
    change R.components.r x.val y.val at hxy
    have hmain : ∀ {a b : α}, R.components.r a b → ∀ (ha : P a) (hb' : P b),
        (R.restrict P hb hw).components.r ⟨a, ha⟩ ⟨b, hb'⟩ := by
      intro a b h
      rw [Ribbon.components, Setoid.sup_def] at h
      change Relation.EqvGen (fun a b => R.black.SameCycle a b ∨ R.white.SameCycle a b) a b at h
      induction h with
      | rel a b hab =>
        intro ha hb'
        rcases hab with hab | hab
        · exact (show SameCycle.setoid (R.restrict P hb hw).black ≤ (R.restrict P hb hw).components from le_sup_left) ((sameCycle_subtypePerm (h := hb)).mpr hab)
        · exact (show SameCycle.setoid (R.restrict P hb hw).white ≤ (R.restrict P hb hw).components from le_sup_right) ((sameCycle_subtypePerm (h := hw)).mpr hab)
      | refl a => exact fun _ _ => (R.restrict P hb hw).components.iseqv.refl _
      | symm a b hab ih =>
        intro ha hb'
        exact (R.restrict P hb hw).components.iseqv.symm (ih hb' ha)
      | trans a b c hab hbc ihab ihbc =>
        intro ha hc
        have hab' : R.components.r a b := by
          rw [Ribbon.components, Setoid.sup_def]
          exact hab
        have hb' : P b := (R.invariant_components P hb hw hab').mp ha
        exact (R.restrict P hb hw).components.iseqv.trans (ihab ha hb') (ihbc hb' hc)
    exact hmain hxy x.prop y.prop

def Ribbon.GenusZero (R : Ribbon α) : Prop :=
  Nat.card (Cycles R.black) + Nat.card (Cycles R.white) + Nat.card (Cycles R.face) =
    Fintype.card α + 2 * Nat.card (Quotient R.components)

lemma Ribbon.planar_restrict (R : Ribbon α) (hR : R.GenusZero) (P : α → Prop) (hb hw) :
    (R.restrict P hb hw).GenusZero := by
  let S := R.restrict P hb hw
  let T := R.restrict (fun x => ¬ P x) (fun x => not_congr (hb x)) (fun x => not_congr (hw x))
  have hs := S.euler_le
  have ht := T.euler_le
  have hbc := cycles_restrict_card_split R.black P hb
  have hwc := cycles_restrict_card_split R.white P hw
  have hfc := cycles_restrict_card_split R.face P (fun x => (hw _).trans (hb x))
  have hcc := quotient_restrict_card_split R.components P (R.invariant_components P hb hw)
  rw [← R.restrict_components P hb hw,
    ← R.restrict_components (fun x => ¬ P x) (fun x => not_congr (hb x))
      (fun x => not_congr (hw x))] at hcc
  have hec : Fintype.card {x // P x} + Fintype.card {x // ¬ P x} = Fintype.card α := by
    have h := Fintype.card_subtype_compl P
    have hle := Fintype.card_subtype_le P
    omega
  change Nat.card (Cycles S.black) + Nat.card (Cycles T.black) = _ at hbc
  change Nat.card (Cycles S.white) + Nat.card (Cycles T.white) = _ at hwc
  change Nat.card (Cycles S.face) + Nat.card (Cycles T.face) = _ at hfc
  change Nat.card (Quotient S.components) + Nat.card (Quotient T.components) = _ at hcc
  unfold Ribbon.GenusZero at hR ⊢
  change Nat.card (Cycles S.black) + Nat.card (Cycles S.white) + Nat.card (Cycles S.face) =
    Fintype.card {x // P x} + 2 * Nat.card (Quotient S.components)
  omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
variable {α : Type portUniverse8} [Fintype α]

omit [Fintype α] in
lemma Ribbon.black_step (R : Ribbon α) (x : α) : R.components.r x (R.black x) :=
  (show SameCycle.setoid R.black ≤ R.components from le_sup_left) (show R.black.SameCycle x (R.black x) from SameCycle.apply_right SameCycle.rfl)

omit [Fintype α] in
lemma Ribbon.white_step (R : Ribbon α) (x : α) : R.components.r x (R.white x) :=
  (show SameCycle.setoid R.white ≤ R.components from le_sup_right) (show R.white.SameCycle x (R.white x) from SameCycle.apply_right SameCycle.rfl)

lemma Ribbon.components_le_of_steps (R : Ribbon α) (s : Setoid α)
    (hb : ∀ x, s.r x (R.black x)) (hw : ∀ x, s.r x (R.white x)) : R.components ≤ s := by
  exact sup_le (fun _ _ h => setoid_sameCycle_of_step s R.black hb h)
    (fun _ _ h => setoid_sameCycle_of_step s R.white hw h)

omit [Fintype α] in
lemma Ribbon.black_component_invariant (R : Ribbon α) (a x : α) :
    R.components.r (R.black x) a ↔ R.components.r x a := by
  constructor
  · exact R.components.iseqv.trans (R.black_step x)
  · exact R.components.iseqv.trans (R.components.iseqv.symm (R.black_step x))

omit [Fintype α] in
lemma Ribbon.white_component_invariant (R : Ribbon α) (a x : α) :
    R.components.r (R.white x) a ↔ R.components.r x a := by
  constructor
  · exact R.components.iseqv.trans (R.white_step x)
  · exact R.components.iseqv.trans (R.components.iseqv.symm (R.white_step x))

def Ribbon.keepComponent (R : Ribbon α) (a : α) : Ribbon {x // R.components.r x a} :=
  R.restrict (fun x => R.components.r x a) (R.black_component_invariant a)
    (R.white_component_invariant a)

lemma Ribbon.keepComponent_card (R : Ribbon α) (a : α) :
    Nat.card (Quotient (R.keepComponent a).components) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨Quotient.mk _ ⟨a, R.components.iseqv.refl a⟩, ?_⟩
  intro c
  induction c using Quotient.inductionOn with
  | h x =>
    apply Quotient.sound
    change (R.restrict _ _ _).components.r x ⟨a, _⟩
    rw [R.restrict_components]
    exact x.prop

lemma Ribbon.spherical_keepComponent (R : Ribbon α) (hR : R.GenusZero) (a : α) :
    (R.keepComponent a).Spherical := by
  have h := R.planar_restrict hR (fun x => R.components.r x a)
    (R.black_component_invariant a) (R.white_component_invariant a)
  change (R.keepComponent a).GenusZero at h
  unfold Ribbon.GenusZero at h
  rw [R.keepComponent_card] at h
  exact h

omit [Fintype α] in
lemma joinPair_left_iff (s : Setoid α) (a b y : α) :
    (joinPair s a b).r a y ↔ s.r a y ∨ s.r b y := by
  change mergeClass s a b a = mergeClass s a b y ↔ _
  have ha : mergeClass s a b a = Quotient.mk s a := by simp [mergeClass]
  rw [ha]
  by_cases hy : Quotient.mk s y = Quotient.mk s b
  · simp only [mergeClass, hy, ite_true, true_iff]
    exact Or.inr (s.iseqv.symm (Quotient.exact hy))
  · simp only [mergeClass, hy, ite_false, Quotient.eq]
    exact or_iff_left (fun h => hy (Quotient.sound (s.iseqv.symm h))) |>.symm

def Ribbon.detach (R : Ribbon α) (a : α) : Ribbon α where
  black := unplug R.black a
  white := unplug R.white a

omit [Fintype α] in
lemma Ribbon.detach_fixed_black (R : Ribbon α) (a : α) : (R.detach a).black a = a :=
  unplug_fixed _ _
omit [Fintype α] in
lemma Ribbon.detach_fixed_white (R : Ribbon α) (a : α) : (R.detach a).white a = a :=
  unplug_fixed _ _

lemma Ribbon.detach_isolated (R : Ribbon α) (a : α) {x : α}
    (h : (R.detach a).components.r a x) : x = a := by
  have hb : ∀ x, (R.detach a).black x = a ↔ x = a := by
    intro x
    constructor
    · intro h
      apply (R.detach a).black.injective
      simpa only [R.detach_fixed_black] using h
    · intro hx
      simpa only [hx] using R.detach_fixed_black a
  have hw : ∀ x, (R.detach a).white x = a ↔ x = a := by
    intro x
    constructor
    · intro h
      apply (R.detach a).white.injective
      simpa only [R.detach_fixed_white] using h
    · intro hx
      simpa only [hx] using R.detach_fixed_white a
  exact ((R.detach a).invariant_components (fun x => x = a) hb hw h).mp rfl

lemma Ribbon.detach_components_le (R : Ribbon α) (a : α) :
    (R.detach a).components ≤ R.components := by
  apply sup_le
  · exact fun _ _ h => (show SameCycle.setoid R.black ≤ R.components from le_sup_left)
      (unplug_sameCycle R.black a h)
  · exact fun _ _ h => (show SameCycle.setoid R.white ≤ R.components from le_sup_right)
      (unplug_sameCycle R.white a h)

lemma Ribbon.components_detach (R : Ribbon α) (a : α) :
    R.components = joinPair (joinPair (R.detach a).components a (R.black a)) a (R.white a) := by
  let s := (R.detach a).components
  let t := joinPair (joinPair s a (R.black a)) a (R.white a)
  apply le_antisymm
  · apply R.components_le_of_steps t
    · intro x
      have hstep : t.r x ((R.detach a).black x) :=
        le_joinPair _ _ _ (le_joinPair _ _ _ ((R.detach a).black_step x))
      have hab : t.r a (R.black a) := le_joinPair _ _ _ (joinPair_related _ _ _)
      have hback : swap a (R.black a) ((R.detach a).black x) = R.black x := by
        simp [Ribbon.detach, unplug]
      rw [← hback]
      exact t.iseqv.trans hstep (setoid_swap_related t hab _)
    · intro x
      have hstep : t.r x ((R.detach a).white x) :=
        le_joinPair _ _ _ (le_joinPair _ _ _ ((R.detach a).white_step x))
      have hab : t.r a (R.white a) := joinPair_related _ _ _
      have hback : swap a (R.white a) ((R.detach a).white x) = R.white x := by
        simp [Ribbon.detach, unplug]
      rw [← hback]
      exact t.iseqv.trans hstep (setoid_swap_related t hab _)
  · apply joinPair_le
    · exact joinPair_le _ _ _ _ (R.detach_components_le a) (R.black_step a)
    · exact R.white_step a

omit [Fintype α] in
lemma Ribbon.detach_face (R : Ribbon α) (a : α) :
    (R.detach a).face = swap a (R.white a) * swap (R.white a) (R.face a) * R.face := by
  simp only [Ribbon.detach, Ribbon.face, unplug, mul_assoc]
  rw [← mul_assoc R.white (swap a (R.black a)), mul_swap_eq_swap_mul]
  simp only [Perm.mul_apply, mul_assoc]

omit [Fintype α] in
lemma Ribbon.detach_face_of_face_fixed (R : Ribbon α) (a : α) (ha : R.face a = a) :
    (R.detach a).face = R.face := by
  rw [R.detach_face, ha, swap_comm (R.white a) a]
  simp

omit [Fintype α] in
lemma Ribbon.detach_face_unplug (R : Ribbon α) (a : α)
    (hw : R.white a ≠ a) (hf : R.face a ≠ a) :
    (R.detach a).face = swap (R.white a) (R.face a) * unplug R.face a := by
  rw [R.detach_face, swap_mul_eq_mul_swap]
  have ha : swap (R.white a) (R.face a) a = a := swap_apply_of_ne_of_ne hw.symm hf.symm
  simp only [swap_inv, ha, swap_apply_left, unplug, mul_assoc]

lemma Ribbon.detach_face_card_le (R : Ribbon α) (a : α) (hw : R.white a ≠ a) :
    Nat.card (Cycles R.face) ≤ Nat.card (Cycles (R.detach a).face) := by
  by_cases hf : R.face a = a
  · rw [R.detach_face_of_face_fixed a hf]
  · have h := swap_cycles_card_le (R.detach a).face (R.white a) (R.face a)
    rw [R.detach_face_unplug a hw hf] at h
    simp only [← mul_assoc, swap_mul_self, one_mul] at h
    have hc := unplug_cycles_card R.face a hf
    rw [R.detach_face_unplug a hw hf]
    omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse9} [Fintype α]

omit [Fintype α] in
lemma Ribbon.face_step (R : Ribbon α) (x : α) : R.components.r x (R.face x) :=
  R.components.iseqv.trans (R.black_step x) (R.white_step (R.black x))

lemma Ribbon.sameCycle_face_components (R : Ribbon α) {x y : α} (h : R.face.SameCycle x y) :
    R.components.r x y := setoid_sameCycle_of_step R.components R.face R.face_step h

lemma Ribbon.detach_components_card (R : Ribbon α) (a : α)
    (hb : R.black a ≠ a) (hw : R.white a ≠ a) :
    Nat.card (Quotient (R.detach a).components) = Nat.card (Quotient R.components) +
      if (R.detach a).components.r (R.black a) (R.white a) then 1 else 2 := by
  let s := (R.detach a).components
  let t := joinPair s a (R.black a)
  have hb' : ¬ s.r a (R.black a) := fun h => hb (R.detach_isolated a h)
  have hw' : ¬ s.r a (R.white a) := fun h => hw (R.detach_isolated a h)
  have ht : Nat.card (Quotient t) + 1 = Nat.card (Quotient s) := joinPair_card s _ _ hb'
  have heq : R.components = joinPair t a (R.white a) := R.components_detach a
  by_cases h : s.r (R.black a) (R.white a)
  · have h' : t.r a (R.white a) := (joinPair_left_iff s _ _ _).mpr (Or.inr h)
    rw [joinPair_eq_of_related _ h'] at heq
    change Nat.card (Quotient s) = Nat.card (Quotient R.components) + if s.r (R.black a) (R.white a) then 1 else 2
    simp only [h, ite_true, heq]
    omega
  · have h' : ¬ t.r a (R.white a) := by
      rw [joinPair_left_iff]
      exact not_or.mpr ⟨hw', h⟩
    have ht' := joinPair_card t a (R.white a) h'
    rw [← heq] at ht'
    change Nat.card (Quotient s) = Nat.card (Quotient R.components) + if s.r (R.black a) (R.white a) then 1 else 2
    simp only [h, ite_false]
    omega

lemma Ribbon.detach_components_card_black_fixed (R : Ribbon α) (a : α)
    (hb : R.black a = a) (hw : R.white a ≠ a) :
    Nat.card (Quotient (R.detach a).components) = Nat.card (Quotient R.components) + 1 := by
  have hn : ¬ (R.detach a).components.r a (R.white a) := fun h => hw (R.detach_isolated a h)
  have heq := R.components_detach a
  rw [hb, joinPair_eq_of_related _ ((R.detach a).components.iseqv.refl a)] at heq
  have hc := joinPair_card (R.detach a).components a (R.white a) hn
  rw [← heq] at hc
  omega

lemma Ribbon.detach_components_card_white_fixed (R : Ribbon α) (a : α)
    (hb : R.black a ≠ a) (hw : R.white a = a) :
    Nat.card (Quotient (R.detach a).components) = Nat.card (Quotient R.components) + 1 := by
  have hn : ¬ (R.detach a).components.r a (R.black a) := fun h => hb (R.detach_isolated a h)
  have heq := R.components_detach a
  rw [hw, joinPair_eq_of_related _ ((joinPair (R.detach a).components a (R.black a)).iseqv.refl a)] at heq
  have hc := joinPair_card (R.detach a).components a (R.black a) hn
  rw [← heq] at hc
  omega

omit [Fintype α] in
lemma Ribbon.detach_face_black_fixed (R : Ribbon α) (a : α) (hb : R.black a = a) :
    (R.detach a).face = unplug R.face a := by
  rw [R.detach_face]
  have hf : R.face a = R.white a := by simp [Ribbon.face, hb]
  simp [hf, unplug]
  rfl

omit [Fintype α] in
lemma Ribbon.detach_face_white_fixed (R : Ribbon α) (a : α) (hw : R.white a = a) :
    (R.detach a).face = unplug R.face a := by
  rw [R.detach_face, hw]
  simp [unplug]
  rfl

lemma Ribbon.detach_face_card_separating (R : Ribbon α) (a : α)
    (hb : R.black a ≠ a) (hw : R.white a ≠ a)
    (hsep : ¬ (R.detach a).components.r (R.black a) (R.white a)) :
    Nat.card (Cycles (R.detach a).face) = Nat.card (Cycles R.face) + 2 := by
  have hf : R.face a ≠ a := by
    intro hf
    have hs : (R.detach a).white (R.black a) = R.white a := by
      change swap a (R.white a) (R.face a) = R.white a
      simp [hf]
    exact hsep (hs ▸ (R.detach a).white_step (R.black a))
  have hs : (R.detach a).white (R.black a) = R.face a := by
    change swap a (R.white a) (R.face a) = R.face a
    exact swap_apply_of_ne_of_ne hf (R.white.injective.ne hb)
  have hnot : ¬ (R.detach a).face.SameCycle (R.white a) (R.face a) := by
    intro h
    have hc := (R.detach a).sameCycle_face_components h
    have hs' := (R.detach a).white_step (R.black a)
    rw [hs] at hs'
    exact hsep ((R.detach a).components.iseqv.trans hs'
      ((R.detach a).components.iseqv.symm hc))
  have hcard := swap_mul_cycles_card (R.detach a).face (R.white a) (R.face a) hnot
  have heq : swap (R.white a) (R.face a) * (R.detach a).face = unplug R.face a := by
    rw [R.detach_face_unplug a hw hf]
    simp [← mul_assoc]
  rw [heq, unplug_cycles_card R.face a hf] at hcard
  omega

theorem Ribbon.genusZero_detach (R : Ribbon α) (hR : R.GenusZero) (a : α) :
    (R.detach a).GenusZero := by
  by_cases hb : R.black a = a
  · have hblack : (R.detach a).black = R.black := by
      simp [Ribbon.detach, unplug, hb]
      rfl
    by_cases hw : R.white a = a
    · have heq : R.detach a = R := by
        cases R
        simp_all [Ribbon.detach, unplug]
      rwa [heq]
    · have hwc := unplug_cycles_card R.white a hw
      have hcc := R.detach_components_card_black_fixed a hb hw
      have hf : R.face a ≠ a := by simpa [Ribbon.face, hb] using hw
      have hfc := unplug_cycles_card R.face a hf
      rw [← R.detach_face_black_fixed a hb] at hfc
      change Nat.card (Cycles (R.detach a).white) = _ at hwc
      unfold Ribbon.GenusZero at hR ⊢
      rw [hblack]
      omega
  · have hbc := unplug_cycles_card R.black a hb
    change Nat.card (Cycles (R.detach a).black) = _ at hbc
    by_cases hw : R.white a = a
    · have hwhite : (R.detach a).white = R.white := by
        simp [Ribbon.detach, unplug, hw]
        rfl
      have hcc := R.detach_components_card_white_fixed a hb hw
      have hf : R.face a ≠ a := by
        intro hf
        apply hb
        apply R.white.injective
        simpa [Ribbon.face, hw] using hf
      have hfc := unplug_cycles_card R.face a hf
      rw [← R.detach_face_white_fixed a hw] at hfc
      unfold Ribbon.GenusZero at hR ⊢
      rw [hwhite]
      omega
    · have hwc := unplug_cycles_card R.white a hw
      change Nat.card (Cycles (R.detach a).white) = _ at hwc
      have hcc := R.detach_components_card a hb hw
      by_cases hs : (R.detach a).components.r (R.black a) (R.white a)
      · rw [ite_eq_left hs] at hcc
        have hfc := R.detach_face_card_le a hw
        have hbound := (R.detach a).euler_le
        unfold Ribbon.GenusZero at hR ⊢
        omega
      · rw [ite_eq_right hs] at hcc
        have hfc := R.detach_face_card_separating a hb hw hs
        unfold Ribbon.GenusZero at hR ⊢
        omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
variable {α : Type portUniverse10} {V : Type portUniverse11} [Fintype α]

lemma Ribbon.mergeWhite_components (R : Ribbon α) (a : α)
    (ha : ¬ R.white.SameCycle a (R.black a)) : (R.mergeWhite a).components = R.components := by
  have hn : ¬ R.white.SameCycle a (R.face a) := by simpa [Ribbon.face] using ha
  apply le_antisymm
  · apply (R.mergeWhite a).components_le_of_steps
    · exact R.black_step
    · intro x
      exact R.components.iseqv.trans (R.white_step x)
        (setoid_swap_related R.components (R.face_step a) (R.white x))
  · apply sup_le
    · exact le_sup_left
    · intro x y h
      exact (show SameCycle.setoid (R.mergeWhite a).white ≤ (R.mergeWhite a).components
        from le_sup_right) (sameCycle_swap_mul R.white a (R.face a) hn h)

lemma Ribbon.genusZero_mergeWhite (R : Ribbon α) (hR : R.GenusZero) (a : α)
    (ha : ¬ R.white.SameCycle a (R.black a)) : (R.mergeWhite a).GenusZero := by
  have hn : ¬ R.white.SameCycle a (R.face a) := by simpa [Ribbon.face] using ha
  have hne : R.face a ≠ a := by intro h; exact hn (by rw [h])
  have hw := swap_mul_cycles_card R.white a (R.face a) hn
  have hf := unplug_cycles_card R.face a hne
  unfold Ribbon.GenusZero at *
  rw [R.mergeWhite_components a ha, mergeWhite_face]
  change Nat.card (Cycles R.black) + Nat.card (Cycles (swap a (R.face a) * R.white)) +
    Nat.card (Cycles (unplug R.face a)) = _
  omega

def Ribbon.mergeBlack (R : Ribbon α) (a : α) : Ribbon α where
  black := swap a (R.black (R.white a)) * R.black
  white := R.white

omit [Fintype α] in
lemma Ribbon.mergeBlack_face (R : Ribbon α) (a : α) :
    (R.mergeBlack a).face = unplug R.face (R.white a) := by
  simp only [Ribbon.mergeBlack, Ribbon.face, unplug, ← mul_assoc]
  rw [mul_swap_eq_swap_mul]
  rfl

lemma Ribbon.mergeBlack_components (R : Ribbon α) (a : α)
    (ha : ¬ R.black.SameCycle a (R.white a)) : (R.mergeBlack a).components = R.components := by
  have hn : ¬ R.black.SameCycle a (R.black (R.white a)) := by simpa using ha
  apply le_antisymm
  · apply (R.mergeBlack a).components_le_of_steps
    · intro x
      exact R.components.iseqv.trans (R.black_step x)
        (setoid_swap_related R.components
          (R.components.iseqv.trans (R.white_step a) (R.black_step (R.white a))) (R.black x))
    · exact R.white_step
  · apply sup_le
    · intro x y h
      exact (show SameCycle.setoid (R.mergeBlack a).black ≤ (R.mergeBlack a).components
        from le_sup_left) (sameCycle_swap_mul R.black a (R.black (R.white a)) hn h)
    · exact le_sup_right

lemma Ribbon.genusZero_mergeBlack (R : Ribbon α) (hR : R.GenusZero) (a : α)
    (ha : ¬ R.black.SameCycle a (R.white a)) : (R.mergeBlack a).GenusZero := by
  have hn : ¬ R.black.SameCycle a (R.black (R.white a)) := by simpa using ha
  have hne : R.face (R.white a) ≠ R.white a := by
    intro h
    have h' : R.black (R.white a) = a := R.white.injective h
    exact hn (by rw [h'])
  have hb := swap_mul_cycles_card R.black a (R.black (R.white a)) hn
  have hf := unplug_cycles_card R.face (R.white a) hne
  unfold Ribbon.GenusZero at *
  rw [R.mergeBlack_components a ha, R.mergeBlack_face]
  change Nat.card (Cycles (swap a (R.black (R.white a)) * R.black)) +
    Nat.card (Cycles R.white) + Nat.card (Cycles (unplug R.face (R.white a))) = _
  omega

omit [Fintype α] in
lemma label_swap (f : α → V) (a b : α) (hab : f a = f b) (x : α) :
    f (swap a b x) = f x := by
  by_cases hxa : x = a
  · subst x
    simpa using hab.symm
  · by_cases hxb : x = b
    · subst x
      simpa using hab
    · rw [swap_apply_of_ne_of_ne hxa hxb]

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse12} [Fintype α]

lemma sameCycle_after_swap {p : Perm α} {a b x y : α} (hab : p.SameCycle a b)
    (hxy : (swap a b * p).SameCycle x y) : p.SameCycle x y := by
  apply setoid_sameCycle_of_step (SameCycle.setoid p) (swap a b * p) _ hxy
  intro z
  exact (SameCycle.apply_right SameCycle.rfl).trans
    (setoid_swap_related (SameCycle.setoid p) hab (p z))

lemma sign_eq_cycles (p : Perm α) :
    sign p = (-1 : ℤˣ) ^ (Fintype.card α - Nat.card (Cycles p)) := by
  classical
  obtain ⟨l, hl, hlen, hmem⟩ := exists_cycle_factorization p
  have hs := sign_prod_list_swap (l := l.map fun ab => swap ab.1 ab.2) (by
    intro g hg
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hg
    exact ⟨ab.1, ab.2, (hmem ab hab).1, rfl⟩)
  rw [hl, List.length_map] at hs
  have hn : Fintype.card α - Nat.card (Cycles p) = l.length := by omega
  rwa [hn]

lemma not_sameCycle_swap_of_sameCycle (p : Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) : ¬ (swap a b * p).SameCycle a b := by
  classical
  intro hq
  let q := swap a b * p
  have hrev : swap a b * q = p := by simp [q, ← mul_assoc]
  have heq : SameCycle.setoid p = SameCycle.setoid q := by
    ext x y
    constructor
    · intro h
      apply sameCycle_after_swap hq
      rwa [hrev]
    · exact sameCycle_after_swap hab
  have hc : Nat.card (Cycles p) = Nat.card (Cycles q) := by rw [Cycles, heq]
  have hs : sign p = sign q := by rw [sign_eq_cycles, sign_eq_cycles, hc]
  have hsign : (-1 : ℤˣ) = 1 := by
    have := hs
    change sign p = sign (swap a b * p) at this
    rw [Perm.sign_mul, sign_swap hne] at this
    exact mul_right_cancel (b := sign p) (by simpa using this.symm)
  norm_num at hsign

lemma swap_mul_cycles_card_split (p : Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) :
    Nat.card (Cycles (swap a b * p)) = Nat.card (Cycles p) + 1 := by
  have h := swap_mul_cycles_card (swap a b * p) a b
    (not_sameCycle_swap_of_sameCycle p a b hne hab)
  simpa [← mul_assoc] using h.symm

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse13} [Fintype α]

def Ribbon.swapBlack (R : Ribbon α) (a b : α) : Ribbon α :=
  ⟨swap a b * R.black, R.white⟩

omit [Fintype α] in
lemma Ribbon.swapBlack_twice (R : Ribbon α) (a b : α) :
    (R.swapBlack a b).swapBlack a b = R := by
  cases R
  simp [Ribbon.swapBlack, ← mul_assoc]

omit [Fintype α] in
lemma Ribbon.swapBlack_face (R : Ribbon α) (a b : α) :
    (R.swapBlack a b).face = swap (R.white a) (R.white b) * R.face := by
  simp only [Ribbon.face, Ribbon.swapBlack, ← mul_assoc]
  rw [mul_swap_eq_swap_mul]

lemma Ribbon.swapBlack_components_merge (R : Ribbon α) (a b : α)
    (hab : ¬ R.black.SameCycle a b) :
    (R.swapBlack a b).components = joinPair R.components a b := by
  apply le_antisymm
  · apply (R.swapBlack a b).components_le_of_steps
    · intro x
      exact (joinPair R.components a b).iseqv.trans
        (le_joinPair _ _ _ (R.black_step x))
        (setoid_swap_related _ (joinPair_related _ _ _) _)
    · intro x
      exact le_joinPair _ _ _ (R.white_step x)
  · apply joinPair_le
    · apply sup_le
      · intro x y hxy
        exact (show SameCycle.setoid (R.swapBlack a b).black ≤
            (R.swapBlack a b).components from le_sup_left)
          (sameCycle_swap_mul R.black a b hab hxy)
      · exact le_sup_right
    · exact (show SameCycle.setoid (R.swapBlack a b).black ≤
          (R.swapBlack a b).components from le_sup_left)
        (swap_mul_sameCycle R.black a b hab)

omit [Fintype α] in
lemma Ribbon.not_blackCycle_of_not_component (R : Ribbon α) {a b : α}
    (h : ¬ R.components.r a b) : ¬ R.black.SameCycle a b :=
  fun hab => h ((show SameCycle.setoid R.black ≤ R.components from le_sup_left) hab)

lemma Ribbon.not_white_faceCycle_of_not_component (R : Ribbon α) {a b : α}
    (h : ¬ R.components.r a b) : ¬ R.face.SameCycle (R.white a) (R.white b) := by
  intro hab
  exact h (R.components.iseqv.trans (R.white_step a)
    (R.components.iseqv.trans (R.sameCycle_face_components hab)
      (R.components.iseqv.symm (R.white_step b))))

lemma Ribbon.genusZero_swapBlack_merge (R : Ribbon α) (hR : R.GenusZero) (a b : α)
    (hab : ¬ R.components.r a b) : (R.swapBlack a b).GenusZero := by
  have hb := R.not_blackCycle_of_not_component hab
  have hbc := swap_mul_cycles_card R.black a b hb
  have hfc := swap_mul_cycles_card R.face (R.white a) (R.white b)
    (R.not_white_faceCycle_of_not_component hab)
  have hcc := joinPair_card R.components a b hab
  rw [← R.swapBlack_components_merge a b hb] at hcc
  rw [← R.swapBlack_face a b] at hfc
  change Nat.card (Cycles (R.swapBlack a b).black) + 1 = _ at hbc
  have hw : (R.swapBlack a b).white = R.white := rfl
  unfold Ribbon.GenusZero at hR ⊢
  rw [hw]
  omega

lemma Ribbon.genusZero_swapBlack_split (R : Ribbon α) (hR : R.GenusZero) (a b : α)
    (hne : a ≠ b) (hab : R.black.SameCycle a b) : (R.swapBlack a b).GenusZero := by
  let S := R.swapBlack a b
  have hback : S.swapBlack a b = R := R.swapBlack_twice a b
  have hn : ¬ S.black.SameCycle a b := not_sameCycle_swap_of_sameCycle R.black a b hne hab
  have hbc := swap_mul_cycles_card_split R.black a b hne hab
  change Nat.card (Cycles S.black) = Nat.card (Cycles R.black) + 1 at hbc
  have hw : S.white = R.white := rfl
  have hcomp := S.swapBlack_components_merge a b hn
  rw [hback] at hcomp
  by_cases hc : S.components.r a b
  · rw [joinPair_eq_of_related S.components hc] at hcomp
    have hfc := swap_cycles_card_le S.face (S.white a) (S.white b)
    rw [← S.swapBlack_face a b, hback] at hfc
    have hbnd := S.euler_le
    unfold Ribbon.GenusZero at hR ⊢
    change Nat.card (Cycles S.black) + Nat.card (Cycles S.white) +
      Nat.card (Cycles S.face) = Fintype.card α + 2 * Nat.card (Quotient S.components)
    rw [hw] at hbnd ⊢
    rw [hcomp] at hR
    omega
  · have hcc := joinPair_card S.components a b hc
    rw [← hcomp] at hcc
    have hfc := swap_mul_cycles_card S.face (S.white a) (S.white b)
      (S.not_white_faceCycle_of_not_component hc)
    rw [← S.swapBlack_face a b, hback] at hfc
    unfold Ribbon.GenusZero at hR ⊢
    change Nat.card (Cycles S.black) + Nat.card (Cycles S.white) +
      Nat.card (Cycles S.face) = Fintype.card α + 2 * Nat.card (Quotient S.components)
    rw [hw]
    omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse14} {V : Type portUniverse15} {F : Type portUniverse16} {A : Type portUniverse17} {B : Type portUniverse18} [sectionInstance2 : Fintype α] [CommGroup A] [Group B]

structure NoncommBalanced (R : Ribbon α) (Inc : V → F → Prop)
    (ι : V → F → (A →* B)) where
  blackLabel : α → V
  whiteLabel : α → F
  blackLabel_rot : ∀ a, blackLabel (R.black a) = blackLabel a
  whiteLabel_rot : ∀ a, whiteLabel (R.white a) = whiteLabel a
  incident : ∀ a, Inc (blackLabel a) (whiteLabel a)
  weight : α → A
  white_prod : ∀ c : Cycles R.white, ∏ a ∈ cycleSet R.white c, weight a = 1
  potential : α → B
  exception : α
  black_balance : ∀ a, a ≠ exception →
    potential (R.black a) = potential a * ι (blackLabel a) (whiteLabel a) (weight a)
  black_defect : potential (R.black exception) ≠ potential exception *
    ι (blackLabel exception) (whiteLabel exception) (weight exception)

def NoncommBalanced.Reduced {R : Ribbon α} {Inc : V → F → Prop}
    {ι : V → F → (A →* B)} (D : NoncommBalanced R Inc ι) : Prop :=
  (∀ a, D.weight a ≠ 1) ∧
  (∀ a, R.black a ≠ a → D.whiteLabel (R.black a) ≠ D.whiteLabel a) ∧
  (∀ a, R.white a ≠ a → D.blackLabel (R.white a) ≠ D.blackLabel a)

lemma cycleClass_perm
    {α : Type contextUniverse1}
    [Fintype.{contextUniverse1} α] (p : Perm α) (a : α) : cycleClass p (p a) = cycleClass p a := by
  apply (cycleClass_eq p _ _).mpr
  exact (SameCycle.refl p a).apply_left

lemma cycleSet_singleton_of_fixed (p : Perm α) (a : α) (h : p a = a) :
    cycleSet p (cycleClass p a) = {a} := by
  classical
  ext b
  rw [mem_cycleSet, cycleClass_eq, Finset.mem_singleton]
  exact ⟨fun hb => hb.eq_of_right h, fun hb => hb ▸ SameCycle.refl p a⟩

lemma cycleSet_card_pow (p : Perm α) (a : α) :
    (p ^ (cycleSet p (cycleClass p a)).card) a = a := by
  classical
  by_cases h : p a = a
  · rw [cycleSet_singleton_of_fixed p a h, Finset.card_singleton, pow_one, h]
  · have heq : cycleSet p (cycleClass p a) = (p.cycleOf a).support := by
      ext b
      rw [mem_cycleSet, cycleClass_eq, mem_support_cycleOf_iff' h, sameCycle_comm]
    rw [heq, ← p.pow_mod_card_support_cycleOf_self_apply]
    simp

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

lemma NoncommBalanced.exception_weight_fixed (D : NoncommBalanced R Inc ι)
    (h : R.black D.exception = D.exception) : D.weight D.exception ≠ 1 := by
  intro hw
  apply D.black_defect
  rw [h, hw, map_one, mul_one]

lemma NoncommBalanced.white_not_fixed (D : NoncommBalanced R Inc ι)
    (hw : ∀ a, D.weight a ≠ 1) (a : α) : R.white a ≠ a := by
  intro h
  have hp := D.white_prod (cycleClass R.white a)
  rw [cycleSet_singleton_of_fixed R.white a h, Finset.prod_singleton] at hp
  exact hw a hp

lemma NoncommBalanced.black_iterate (D : NoncommBalanced R Inc ι)
    (a : α) (ha : ¬ R.black.SameCycle a D.exception) (n : ℕ) :
    D.potential ((R.black^n) a) = D.potential a *
      ((List.range n).map fun k =>
        ι (D.blackLabel ((R.black^k) a)) (D.whiteLabel ((R.black^k) a))
          (D.weight ((R.black^k) a))).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, D.black_balance, ih, List.range_succ,
      List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, mul_assoc]
    intro he
    apply ha
    rw [← he]
    exact (SameCycle.refl R.black a).pow_right (n := n)

end OddKaplansky.Planar

namespace OddKaplansky.Holonomy
open Equiv Equiv.Perm
variable {α : Type portUniverse19} {B : Type portUniverse20} [Group B]

structure Defect (p : Perm α) (w : α → B) where
  potential : α → B
  exception : α
  balance : ∀ x, x ≠ exception → potential (p x) = potential x * w x
  defective : potential (p exception) ≠ potential exception * w exception

noncomputable def combineWeight (w : α → B) (a b x : α) : B :=
  if x = a then 1 else if x = b then w a * w b else w x
noncomputable def combinePotential (t : α → B) (a b x : α) : B :=
  if x = b then t a else t x

def Defect.combine {p : Perm α} {w : α → B} (D : Defect p w)
    (a b : α) (hab : a ≠ b) (hpa : p a = b) :
    Defect p (combineWeight w a b) := by
  classical
  let t := combinePotential D.potential a b
  have hpb : p b ≠ b := by
    intro h
    exact hab (p.injective (hpa.trans h.symm))
  have ht (x : α) (hx : x ≠ b) : t x = D.potential x :=
    ite_eq_right hx
  have hta : t a = D.potential a := ht a hab
  have htb : t b = D.potential a := ite_eq_left rfl
  have hxa (x : α) (hx : x ≠ a) : p x ≠ b := by
    intro h
    exact hx (p.injective (h.trans hpa.symm))
  have hbalance_a : t (p a) = t a * combineWeight w a b a := by
    rw [hpa, htb, hta]
    simp [combineWeight]
  have hbalance_b (ha : a ≠ D.exception) (hb : b ≠ D.exception) :
      t (p b) = t b * combineWeight w a b b := by
    rw [ht _ hpb, htb, D.balance b hb, ← hpa, D.balance a ha, hpa]
    simp [combineWeight, hab.symm, mul_assoc]
  have hbalance_other (x : α) (hxa' : x ≠ a) (hxb : x ≠ b)
      (hxe : x ≠ D.exception) : t (p x) = t x * combineWeight w a b x := by
    rw [ht _ (hxa x hxa'), ht _ hxb, D.balance x hxe]
    simp [combineWeight, hxa', hxb]
  by_cases hea : D.exception = a
  · refine ⟨t, b, ?_, ?_⟩
    · intro x hxb
      by_cases hxa' : x = a
      · subst x; exact hbalance_a
      · exact hbalance_other x hxa' hxb (by simpa [hea] using hxa')
    · intro h
      have he := D.defective
      rw [hea, hpa] at he
      apply he
      rw [ht _ hpb, htb, D.balance b (by simpa [hea] using hab.symm)] at h
      simp [combineWeight, hab.symm, ← mul_assoc] at h
      exact h
  · refine ⟨t, D.exception, ?_, ?_⟩
    · intro x hxe
      by_cases hxa' : x = a
      · subst x; exact hbalance_a
      · by_cases hxb : x = b
        · subst x; exact hbalance_b (Ne.symm hea) hxe
        · exact hbalance_other x hxa' hxb hxe
    · intro h
      apply D.defective
      by_cases heb : D.exception = b
      · rw [heb, ht _ hpb, htb, show combineWeight w a b b = w a * w b by
          simp [combineWeight, hab.symm]] at h
        rw [heb]
        have htba := D.balance a (Ne.symm hea)
        rw [hpa] at htba
        rw [htba, mul_assoc]
        exact h
      · rw [ht _ (hxa _ hea), ht _ heb] at h
        simpa [combineWeight, hea, heb] using h

def Defect.merge {p : Perm α} {w : α → B} (D : Defect p w)
    (a b : α) (hab : ¬ p.SameCycle a b) : Defect (swap a b * p) w := by
  classical
  let u : B := D.potential a * (D.potential b)⁻¹
  let k (x : α) : B := if p.SameCycle b x then u else 1
  let t (x : α) : B := k x * D.potential x
  have hba : ¬ p.SameCycle b a := fun h => hab h.symm
  have hka : k a = 1 := ite_eq_right hba
  have hkb : k b = u := ite_eq_left (SameCycle.refl p b)
  have hkp (x : α) : k (p x) = k x := by simp only [k, sameCycle_apply_right]
  have htarget (x : α) : t ((swap a b * p) x) = k x * D.potential (p x) := by
    by_cases hxa : p x = a
    · have hkx : k x = 1 := by rw [← hkp, hxa, hka]
      simp [Perm.mul_apply, hxa, t, hkb, hkx, u]
    · by_cases hxb : p x = b
      · have hkx : k x = u := by rw [← hkp, hxb, hkb]
        simp [Perm.mul_apply, hxb, t, hka, hkx, u]
      · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxb]
        change k (p x) * D.potential (p x) = _
        rw [hkp]
  refine ⟨t, D.exception, ?_, ?_⟩
  · intro x hx
    rw [htarget, D.balance x hx, ← mul_assoc]
  · intro h
    apply D.defective
    rw [htarget] at h
    change k D.exception * D.potential (p D.exception) =
      k D.exception * D.potential D.exception * w D.exception at h
    rw [mul_assoc] at h
    exact mul_left_cancel h

def Defect.swapEqual {p : Perm α} {w : α → B} (D : Defect p w)
    (a b : α) (hab : D.potential a = D.potential b) :
    Defect (swap a b * p) w := by
  classical
  have ht (x : α) : D.potential ((swap a b * p) x) = D.potential (p x) := by
    apply OddKaplansky.Planar.label_swap
    exact hab
  refine ⟨D.potential, D.exception, ?_, ?_⟩
  · intro x hx
    rw [ht]
    exact D.balance x hx
  · rw [ht]
    exact D.defective

def Defect.restrict {p : Perm α} {w : α → B} (D : Defect p w)
    (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) (he : P D.exception) :
    Defect (p.subtypePerm hP) (fun x => w x.val) where
  potential x := D.potential x.val
  exception := ⟨D.exception, he⟩
  balance x hx := D.balance x (fun h => hx (Subtype.ext h))
  defective := D.defective

def Defect.splitRestrict {p : Perm α} {w : α → B} (D : Defect p w)
    (a b : α) (hab : D.potential a ≠ D.potential b)
    (P : α → Prop) (hP : ∀ x, P ((swap a b * p) x) ↔ P x)
    (ha : P a) (hb : ¬ P b) (he : ¬ P D.exception) :
    Defect ((swap a b * p).subtypePerm hP) (fun x => w x.val) := by
  classical
  have hab' : a ≠ b := fun h => hab (congrArg D.potential h)
  have hq : (swap a b * p) (p.symm b) = a := by simp
  have hd : P (p.symm b) := (hP _).mp (by rw [hq]; exact ha)
  refine ⟨(fun x => D.potential x.val), ⟨p.symm b, hd⟩, ?_, ?_⟩
  · intro x hx
    have hxe : x.val ≠ D.exception := fun h => he (h ▸ x.prop)
    have hxb : p x.val ≠ b := by
      intro h
      apply hx
      apply Subtype.ext
      exact p.injective (h.trans (p.apply_symm_apply b).symm)
    have hxa : p x.val ≠ a := by
      intro h
      have hqx : (swap a b * p) x.val = b := by simp [Perm.mul_apply, h]
      exact hb (hqx ▸ (hP x).mpr x.prop)
    change D.potential ((swap a b * p) x.val) = D.potential x.val * w x.val
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxb]
    exact D.balance x hxe
  · change D.potential ((swap a b * p) (p.symm b)) ≠
      D.potential (p.symm b) * w (p.symm b)
    rw [hq, ← D.balance (p.symm b) (fun h => he (h ▸ hd)), p.apply_symm_apply]
    exact hab

def Defect.unplug {p : Perm α} {w : α → B} (D : Defect p w)
    (a : α) (hwa : w a = 1) : Defect (OddKaplansky.Planar.unplug p a) w := by
  classical
  by_cases hpa : p a = a
  · have hq : OddKaplansky.Planar.unplug p a = p := by
      ext x
      simp [OddKaplansky.Planar.unplug, hpa]
    rw [hq]
    exact D
  let b := p.symm a
  have hpb : p b = a := p.apply_symm_apply a
  have hba : b ≠ a := by
    intro h
    apply hpa
    rwa [h] at hpb
  let q := OddKaplansky.Planar.unplug p a
  have hqa : q a = a := OddKaplansky.Planar.unplug_fixed p a
  have hqb : q b = p a := by simp [q, OddKaplansky.Planar.unplug, hpb]
  have hqx (x : α) (hxa : x ≠ a) (hxb : x ≠ b) : q x = p x := by
    have hpxa : p x ≠ a := fun h => hxb (p.injective (h.trans hpb.symm))
    have hpxpa : p x ≠ p a := fun h => hxa (p.injective h)
    exact swap_apply_of_ne_of_ne hpxa hpxpa
  have hbalance_a : D.potential (q a) = D.potential a * w a := by rw [hqa, hwa, mul_one]
  by_cases hea : D.exception = a
  · refine ⟨D.potential, b, ?_, ?_⟩
    · intro x hxb
      by_cases hxa : x = a
      · subst x; exact hbalance_a
      · rw [hqx x hxa hxb]
        exact D.balance x (by simpa [hea] using hxa)
    · intro h
      apply D.defective
      have hh := D.balance b (by simpa [hea] using hba)
      rw [hpb] at hh
      change D.potential (q b) = D.potential b * w b at h
      rw [hqb, ← hh] at h
      simpa [hea, hwa] using h
  · have ha : D.potential (p a) = D.potential a := by
      simpa [hwa] using D.balance a (Ne.symm hea)
    refine ⟨D.potential, D.exception, ?_, ?_⟩
    · intro x hxe
      by_cases hxa : x = a
      · subst x; exact hbalance_a
      · by_cases hxb : x = b
        · subst x
          rw [hqb, ha, ← hpb]
          exact D.balance b hxe
        · rw [hqx x hxa hxb]
          exact D.balance x hxe
    · intro h
      apply D.defective
      by_cases heb : D.exception = b
      · change D.potential (q D.exception) = _ at h
        rw [heb, hqb, ha] at h
        simpa [heb, hpb] using h
      · rw [hqx D.exception hea heb] at h
        exact h

end OddKaplansky.Holonomy

namespace OddKaplansky.Planar
open Equiv Equiv.Perm OddKaplansky.Holonomy
variable {α : Type portUniverse21} {β : Type portUniverse22} {V : Type portUniverse23} {F : Type portUniverse24} {A : Type portUniverse25} {B : Type portUniverse26} [sectionInstance3 : Fintype α] [CommGroup A] [Group B]

def cycleMap {p q : Perm α} (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) :
    Cycles p → Cycles q := Quotient.map id (fun _ _ hxy => h hxy)

omit [Fintype α] in
lemma cycleMap_class {p q : Perm α} (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y)
    (a : α) : cycleMap h (cycleClass p a) = cycleClass q a := rfl

lemma prod_cycle_coarsen {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) (c : Cycles q) (f : α → A) :
    ∏ a ∈ cycleSet q c, f a =
      ∏ d ∈ Finset.univ.filter (fun d : Cycles p => cycleMap h d = c),
        ∏ a ∈ cycleSet p d, f a := by
  classical
  have hh := Finset.prod_fiberwise_eq_prod_filter (Finset.univ : Finset α)
    (Finset.univ.filter (fun d : Cycles p => cycleMap h d = c)) (cycleClass p) f
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, cycleMap_class, cycleSet]
    using hh.symm

lemma prod_cycle_coarsen_one {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) (f : α → A)
    (hf : ∀ c : Cycles p, ∏ a ∈ cycleSet p c, f a = 1) (c : Cycles q) :
    ∏ a ∈ cycleSet q c, f a = 1 := by
  rw [prod_cycle_coarsen h]
  simp only [hf, Finset.prod_const_one]

lemma label_sameCycle (p : Perm α) (f : α → β) (hf : ∀ a, f (p a) = f a)
    {x y : α} (hxy : p.SameCycle x y) : f x = f y :=
  setoid_sameCycle_of_step (Setoid.ker f) p (fun x => (hf x).symm) hxy

lemma label_unplug (p : Perm α) (f : α → β) (hf : ∀ a, f (p a) = f a) (a x : α) :
    f (unplug p a x) = f x :=
  (label_sameCycle p f hf (unplug_sameCycle p a ((SameCycle.refl _ x).apply_right))).symm

lemma sameCycle_unplug_iff_of_ne (p : Perm α) (a : α) {x y : α}
    (hx : x ≠ a) (hy : y ≠ a) : (unplug p a).SameCycle x y ↔ p.SameCycle x y := by
  by_cases ha : p a = a
  · simp only [unplug, ha, swap_self]
    rfl
  · exact unplug_sameCycle_iff p a ha hx hy

lemma cycleSet_unplug (p : Perm α) (a x : α) (hx : x ≠ a) :
    cycleSet (unplug p a) (cycleClass (unplug p a) x) =
      (cycleSet p (cycleClass p x)).erase a := by
  classical
  ext y
  rw [mem_cycleSet, cycleClass_eq, Finset.mem_erase, mem_cycleSet, cycleClass_eq]
  constructor
  · intro hy
    refine ⟨?_, unplug_sameCycle p a hy⟩
    intro hya
    subst y
    exact hx (hy.symm.eq_of_right (unplug_fixed p a))
  · rintro ⟨hya, hy⟩
    exact (sameCycle_unplug_iff_of_ne p a hya hx).mpr hy

omit [Fintype α] in
lemma prod_erase_of_one (s : Finset α) (a : α) (f : α → A) (ha : f a = 1) :
    ∏ x ∈ s.erase a, f x = ∏ x ∈ s, f x := by
  classical
  apply Finset.prod_subset (Finset.erase_subset _ _)
  intro x hx hxa
  have : x = a := by simpa [hx] using hxa
  simpa [this] using ha

lemma prod_cycle_unplug (p : Perm α) (a x : α) (hx : x ≠ a)
    (f : α → A) (ha : f a = 1) :
    ∏ y ∈ cycleSet (unplug p a) (cycleClass (unplug p a) x), f y =
      ∏ y ∈ cycleSet p (cycleClass p x), f y := by
  rw [cycleSet_unplug p a x hx]
  exact prod_erase_of_one _ a f ha

def cycleSubtypeMap (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    Cycles (p.subtypePerm hP) → Cycles p :=
  Quotient.map Subtype.val (fun _ _ h => (sameCycle_subtypePerm (h := hP)).mp h)

omit [Fintype α] in
lemma cycleSubtypeMap_injective (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    Function.Injective (cycleSubtypeMap p P hP) := by
  intro c d
  induction c using Quotient.inductionOn with
  | h x =>
    induction d using Quotient.inductionOn with
    | h y =>
      intro h
      exact Quotient.sound ((sameCycle_subtypePerm (h := hP)).mpr (Quotient.exact h))

lemma prod_cycle_subtype (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x)
    (c : Cycles (p.subtypePerm hP)) (f : α → A) :
    ∏ a ∈ cycleSet (p.subtypePerm hP) c, f a.val =
      ∏ a ∈ cycleSet p (cycleSubtypeMap p P hP c), f a := by
  classical
  induction c using Quotient.inductionOn with
  | h x =>
    apply Finset.prod_bij (fun y _ => y.val)
    · intro y hy
      apply (mem_cycleSet _ _ _).mpr
      exact Quotient.sound ((sameCycle_subtypePerm (h := hP)).mp
        (Quotient.exact ((mem_cycleSet _ _ _).mp hy)))
    · intro y _ z _ h
      exact Subtype.ext h
    · intro y hy
      have hcycle : p.SameCycle y x.val := (cycleClass_eq _ _ _).mp ((mem_cycleSet _ _ _).mp hy)
      have hPy : P y := (perm_invariant_cycle p P hP hcycle).mpr x.property
      refine ⟨⟨y, hPy⟩, ?_, rfl⟩
      apply (mem_cycleSet _ _ _).mpr
      exact Quotient.sound ((sameCycle_subtypePerm (h := hP)).mpr hcycle)
    · intro _ _
      rfl

lemma prod_combineWeight
    {α : Type contextUniverse1}
    {A : Type contextUniverse2}
    [Fintype.{contextUniverse1} α]
    [CommGroup.{contextUniverse2} A] (s : Finset α) (w : α → A) (a b : α) (hab : a ≠ b)
    (hmem : a ∈ s ↔ b ∈ s) : ∏ x ∈ s, combineWeight w a b x = ∏ x ∈ s, w x := by
  classical
  have heq (x : α) : combineWeight w a b x =
      w x * (if x = b then w a else 1) / (if x = a then w a else 1) := by
    by_cases hxa : x = a
    · subst x; simp [combineWeight, hab]
    · by_cases hxb : x = b
      · subst x; simp [combineWeight, hab.symm, mul_comm]
      · simp [combineWeight, hxa, hxb]
  simp only [heq, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp only [hmem, mul_div_cancel_right]

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

def NoncommBalanced.localWeight (D : NoncommBalanced R Inc ι) (x : α) : B :=
  ι (D.blackLabel x) (D.whiteLabel x) (D.weight x)

def NoncommBalanced.defect (D : NoncommBalanced R Inc ι) : Defect R.black D.localWeight :=
  ⟨D.potential, D.exception, D.black_balance, D.black_defect⟩

def NoncommBalanced.withDefect (D : NoncommBalanced R Inc ι) (w : α → A)
    (hw : ∀ c : Cycles R.white, ∏ x ∈ cycleSet R.white c, w x = 1)
    (E : Defect R.black (fun x => ι (D.blackLabel x) (D.whiteLabel x) (w x))) :
    NoncommBalanced R Inc ι :=
  { D with
    weight := w
    white_prod := hw
    potential := E.potential
    exception := E.exception
    black_balance := E.balance
    black_defect := E.defective }

def NoncommBalanced.combine (D : NoncommBalanced R Inc ι) (a b : α)
    (hab : a ≠ b) (hpa : R.black a = b) (hw : R.white.SameCycle a b) :
    NoncommBalanced R Inc ι := by
  have hbl : D.blackLabel b = D.blackLabel a := by rw [← hpa, D.blackLabel_rot]
  have hwl : D.whiteLabel b = D.whiteLabel a :=
    (label_sameCycle R.white D.whiteLabel D.whiteLabel_rot hw).symm
  have hm : (fun x => ι (D.blackLabel x) (D.whiteLabel x) (combineWeight D.weight a b x)) =
      combineWeight D.localWeight a b := by
    funext x
    by_cases hxa : x = a
    · subst x; simp [combineWeight]
    · by_cases hxb : x = b
      · subst x; simp [combineWeight, hab.symm, NoncommBalanced.localWeight, hbl, hwl]
      · simp [combineWeight, hxa, hxb, NoncommBalanced.localWeight]
  refine D.withDefect (combineWeight D.weight a b) ?_ ?_
  · intro c
    rw [prod_combineWeight _ _ _ _ hab]
    · exact D.white_prod c
    · rw [mem_cycleSet, mem_cycleSet, (cycleClass_eq R.white a b).mpr hw]
  · rw [hm]
    exact D.defect.combine a b hab hpa

def NoncommBalanced.restrict (D : NoncommBalanced R Inc ι) (P : α → Prop)
    (hb : ∀ x, P (R.black x) ↔ P x) (hw : ∀ x, P (R.white x) ↔ P x)
    (he : P D.exception) : NoncommBalanced (R.restrict P hb hw) Inc ι where
  blackLabel x := D.blackLabel x.val
  whiteLabel x := D.whiteLabel x.val
  blackLabel_rot x := D.blackLabel_rot x.val
  whiteLabel_rot x := D.whiteLabel_rot x.val
  incident x := D.incident x.val
  weight x := D.weight x.val
  white_prod c := by
    dsimp only [Ribbon.restrict] at c ⊢
    rw [prod_cycle_subtype R.white P hw c D.weight]
    exact D.white_prod _
  potential x := D.potential x.val
  exception := ⟨D.exception, he⟩
  black_balance x hx := D.black_balance x.val (fun h => hx (Subtype.ext h))
  black_defect := D.black_defect

def NoncommBalanced.detach (D : NoncommBalanced R Inc ι) (a : α) (ha : D.weight a = 1) :
    NoncommBalanced (R.detach a) Inc ι := by
  let E := D.defect.unplug a (by simp [NoncommBalanced.localWeight, ha])
  refine { D with
    blackLabel_rot := label_unplug R.black D.blackLabel D.blackLabel_rot a
    whiteLabel_rot := label_unplug R.white D.whiteLabel D.whiteLabel_rot a
    potential := E.potential
    exception := E.exception
    white_prod := ?_
    black_balance := E.balance
    black_defect := E.defective }
  intro c
  induction c using Quotient.inductionOn with
  | h x =>
    change (∏ y ∈ cycleSet (unplug R.white a) (cycleClass (unplug R.white a) x), D.weight y) = 1
    by_cases hx : x = a
    · subst x
      rw [cycleSet_singleton_of_fixed _ _ (unplug_fixed R.white a), Finset.prod_singleton, ha]
    · rw [prod_cycle_unplug R.white a x hx D.weight ha]
      exact D.white_prod _

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm OddKaplansky.Holonomy
universe u
variable {α : Type u} {V : Type portUniverse27} {F : Type portUniverse28} {A : Type portUniverse29} {B : Type portUniverse30} [Fintype α] [CommGroup A] [Group B]
variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

def NoncommBalanced.mergeWhite (D : NoncommBalanced R Inc ι) (a : α)
    (ha : ¬ R.white.SameCycle a (R.black a))
    (hl : D.whiteLabel (R.black a) = D.whiteLabel a) :
    NoncommBalanced (R.mergeWhite a) Inc ι := by
  have hn : ¬ R.white.SameCycle a (R.face a) := by simpa [Ribbon.face] using ha
  have hlabel : D.whiteLabel a = D.whiteLabel (R.face a) := by
    rw [Ribbon.face, Perm.mul_apply, D.whiteLabel_rot, hl]
  refine { D with whiteLabel_rot := ?_, white_prod := ?_ }
  · intro x
    change D.whiteLabel (swap a (R.face a) (R.white x)) = D.whiteLabel x
    rw [label_swap D.whiteLabel a (R.face a) hlabel, D.whiteLabel_rot]
  · intro c
    exact prod_cycle_coarsen_one (sameCycle_swap_mul R.white a (R.face a) hn)
      D.weight D.white_prod c

def NoncommBalanced.spliceBlack (D : NoncommBalanced R Inc ι) (a b : α)
    (hl : D.blackLabel a = D.blackLabel b)
    (E : Defect (swap a b * R.black) D.localWeight) :
    NoncommBalanced (R.swapBlack a b) Inc ι := by
  refine { D with
    blackLabel_rot := ?_
    potential := E.potential
    exception := E.exception
    black_balance := E.balance
    black_defect := E.defective }
  intro x
  change D.blackLabel (swap a b (R.black x)) = D.blackLabel x
  rw [label_swap D.blackLabel a b hl, D.blackLabel_rot]

omit [Fintype α] in
lemma fixed_compl_invariant (p : Perm α) (a : α) (ha : p a = a) (x : α) :
    p x ≠ a ↔ x ≠ a := by
  constructor
  · intro h hxa; subst x; exact h ha
  · intro h hpx; exact h (p.injective (hpx.trans ha.symm))

lemma NoncommBalanced.exists_smaller (D : NoncommBalanced R Inc ι) (hR : R.GenusZero)
    (a : α) (ha : D.weight a = 1) :
    ∃ (β : Type u) (iβ : Fintype β) (S : Ribbon β),
      @Fintype.card β iβ < Fintype.card α ∧ @Ribbon.GenusZero β iβ S ∧
        Nonempty (@NoncommBalanced β V F A B iβ _ _ S Inc ι) := by
  classical
  let D' := D.detach a ha
  have hea : D'.exception ≠ a := by
    intro he
    apply D'.black_defect
    rw [he]
    change D'.potential ((R.detach a).black a) =
      D'.potential a * ι (D.blackLabel a) (D.whiteLabel a) (D.weight a)
    rw [R.detach_fixed_black a, ha, map_one, mul_one]
  let hb := fixed_compl_invariant (R.detach a).black a (R.detach_fixed_black a)
  let hw := fixed_compl_invariant (R.detach a).white a (R.detach_fixed_white a)
  let S := (R.detach a).restrict (fun x => x ≠ a) hb hw
  have hcard : Fintype.card {x : α // x ≠ a} < Fintype.card α :=
    Fintype.card_subtype_lt (x := a) (by simp)
  refine ⟨{x : α // x ≠ a}, _, S, ?_,
    (R.detach a).planar_restrict (R.genusZero_detach hR a) (fun x : α => x ≠ a) hb hw, ?_⟩
  · convert hcard
  · exact ⟨D'.restrict (fun x => x ≠ a) hb hw hea⟩

lemma Ribbon.mergeBlack_separates (R : Ribbon α) (hR : R.GenusZero) (a : α)
    (hne : a ≠ R.black (R.white a))
    (hs : R.black.SameCycle a (R.black (R.white a))) :
    ¬ (R.mergeBlack a).components.r a (R.black (R.white a)) := by
  let b := R.black (R.white a)
  let S := R.swapBlack a b
  have hback : S.swapBlack a b = R := R.swapBlack_twice a b
  have hn : ¬ S.black.SameCycle a b := not_sameCycle_swap_of_sameCycle R.black a b hne hs
  have hbc := swap_mul_cycles_card_split R.black a b hne hs
  have hf : R.face (R.white a) ≠ R.white a := by
    intro h
    exact hne (R.white.injective h).symm
  have hfc := unplug_cycles_card R.face (R.white a) hf
  rw [← R.mergeBlack_face a] at hfc
  have hcomp := S.swapBlack_components_merge a b hn
  rw [hback] at hcomp
  intro hc
  change S.components.r a b at hc
  rw [joinPair_eq_of_related S.components hc] at hcomp
  have hbnd := S.euler_le
  change Nat.card (Cycles S.black) = Nat.card (Cycles R.black) + 1 at hbc
  change Nat.card (Cycles S.face) = Nat.card (Cycles R.face) + 1 at hfc
  have hw : S.white = R.white := rfl
  rw [hw, ← hcomp] at hbnd
  unfold Ribbon.GenusZero at hR
  omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse31} {V : Type portUniverse32} {F : Type portUniverse33} {A : Type portUniverse34} {B : Type portUniverse35} [Fintype α] [CommGroup A] [Group B]

structure ShortWords (Inc : V → F → Prop) (ι : V → F → (A →* B)) : Prop where
  one : ∀ v f, Inc v f → ∀ a, a ≠ 1 → ι v f a ≠ 1
  two : ∀ v f g, Inc v f → Inc v g → f ≠ g →
    ∀ a b, a ≠ 1 → b ≠ 1 → ι v f a * ι v g b ≠ 1
  three : ∀ v f g h, Inc v f → Inc v g → Inc v h →
    f ≠ g → g ≠ h → h ≠ f →
    ∀ a b c, a ≠ 1 → b ≠ 1 → c ≠ 1 → ι v f a * ι v g b * ι v h c ≠ 1

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

lemma NoncommBalanced.black_fixed_exception (D : NoncommBalanced R Inc ι)
    (hred : D.Reduced) (hshort : ShortWords Inc ι) (a : α) (ha : R.black a = a) :
    a = D.exception := by
  by_contra hn
  have h := D.black_balance a hn
  rw [ha] at h
  apply hshort.one _ _ (D.incident a) _ (hred.1 a)
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

lemma NoncommBalanced.cycle_product_eq_one (D : NoncommBalanced R Inc ι)
    (a : α) (ha : ¬ R.black.SameCycle a D.exception) (n : ℕ)
    (hn : (R.black^n) a = a) :
    ((List.range n).map fun k =>
      ι (D.blackLabel ((R.black^k) a)) (D.whiteLabel ((R.black^k) a))
        (D.weight ((R.black^k) a))).prod = 1 := by
  have h := D.black_iterate a ha n
  rw [hn] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

lemma NoncommBalanced.black_degree (D : NoncommBalanced R Inc ι) (hred : D.Reduced)
    (hshort : ShortWords Inc ι) (c : Cycles R.black) :
    4 ≤ (cycleSet R.black c).card + if c = cycleClass R.black D.exception then 3 else 0 := by
  classical
  have hpos := (cycleSet_nonempty R.black c).card_pos
  by_cases hc : c = cycleClass R.black D.exception
  · rw [ite_eq_left hc]; omega
  rw [ite_eq_right hc, add_zero]
  obtain ⟨a, ha⟩ := cycleSet_nonempty R.black c
  have hac : cycleClass R.black a = c := (mem_cycleSet _ _ _).mp ha
  have hae : ¬ R.black.SameCycle a D.exception := by
    intro h
    exact hc (hac.symm.trans ((cycleClass_eq _ _ _).mpr h))
  have hb : D.blackLabel (R.black a) = D.blackLabel a := D.blackLabel_rot a
  have hbb : D.blackLabel ((R.black^2) a) = D.blackLabel a := by
    simp only [pow_two, Perm.mul_apply, D.blackLabel_rot]
  have hp (n : ℕ) (hn : (cycleSet R.black c).card = n) : (R.black^n) a = a := by
    rw [← hn, ← hac]
    exact cycleSet_card_pow R.black a
  have hnf (hcard : 1 < (cycleSet R.black c).card) : R.black a ≠ a := by
    intro h
    rw [← hac, cycleSet_singleton_of_fixed R.black a h, Finset.card_singleton] at hcard
    omega
  by_contra! hcard
  have hs : (cycleSet R.black c).card = 1 ∨ (cycleSet R.black c).card = 2 ∨
      (cycleSet R.black c).card = 3 := by omega
  rcases hs with h1 | h2 | h3
  · have hz := D.cycle_product_eq_one a hae 1 (hp 1 h1)
    simp at hz
    exact hshort.one _ _ (D.incident a) _ (hred.1 a) hz
  · have hz := D.cycle_product_eq_one a hae 2 (hp 2 h2)
    simp [List.range_succ, hb] at hz
    have hi : Inc (D.blackLabel a) (D.whiteLabel (R.black a)) := by
      rw [← hb]; exact D.incident _
    exact hshort.two _ _ _ (D.incident a) hi
      (hred.2.1 a (hnf (by omega))).symm _ _ (hred.1 a) (hred.1 _) hz
  · have hz := D.cycle_product_eq_one a hae 3 (hp 3 h3)
    simp [List.range_succ, hb, hbb] at hz
    have hi : Inc (D.blackLabel a) (D.whiteLabel (R.black a)) := by
      rw [← hb]; exact D.incident _
    have hj : Inc (D.blackLabel a) (D.whiteLabel ((R.black^2) a)) := by
      rw [← hbb]; exact D.incident _
    have hnf₀ := hnf (by omega)
    have hnf₁ : R.black (R.black a) ≠ R.black a := fun h => hnf₀ (R.black.injective h)
    have hnf₂ : R.black ((R.black^2) a) ≠ (R.black^2) a := by
      intro h
      exact hnf₀ (((SameCycle.refl R.black a).pow_right (n := 2)).apply_eq_self_iff.mpr h)
    have h01 := (hred.2.1 a hnf₀).symm
    have h12 : D.whiteLabel (R.black a) ≠ D.whiteLabel ((R.black^2) a) := by
      simpa only [pow_two, Perm.mul_apply] using (hred.2.1 (R.black a) hnf₁).symm
    have h20 : D.whiteLabel ((R.black^2) a) ≠ D.whiteLabel a := by
      have hh := (hred.2.1 ((R.black^2) a) hnf₂).symm
      have hh' : R.black ((R.black^2) a) = a := by
        simpa only [show 3 = 2+1 from rfl, pow_succ', Perm.mul_apply] using hp 3 h3
      rwa [hh'] at hh
    apply hshort.three _ _ _ _ (D.incident a) hi hj h01 h12 h20 _ _ _
      (hred.1 a) (hred.1 _) (hred.1 _)
    simpa only [mul_assoc] using hz

lemma NoncommBalanced.white_degree (D : NoncommBalanced R Inc ι) (hred : D.Reduced)
    (c : Cycles R.white) : 2 ≤ (cycleSet R.white c).card := by
  have hpos := (cycleSet_nonempty R.white c).card_pos
  by_contra! h
  have hc : (cycleSet R.white c).card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have hz := D.white_prod c
  rw [ha, Finset.prod_singleton] at hz
  exact hred.1 a hz

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse36} {V : Type portUniverse37} {F : Type portUniverse38} {A : Type portUniverse39} {B : Type portUniverse40} [Fintype α] [CommGroup A] [Group B]

def incidenceGraph (Inc : V → F → Prop) : SimpleGraph (Sum V F) where
  Adj x y := match x, y with
    | .inl v, .inr f => Inc v f
    | .inr f, .inl v => Inc v f
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

def NoncommBalanced.exceptionFace (D : NoncommBalanced R Inc ι) : Cycles R.face :=
  cycleClass R.face D.exception

lemma NoncommBalanced.black_not_fixed_on_other_face (D : NoncommBalanced R Inc ι)
    (hred : D.Reduced) (hshort : ShortWords Inc ι) {a : α}
    (ha : cycleClass R.face a ≠ D.exceptionFace) : R.black a ≠ a := by
  intro h
  apply ha
  rw [D.black_fixed_exception hred hshort a h]
  rfl

def NoncommBalanced.halfStep (D : NoncommBalanced R Inc ι) (a : α) :
    (incidenceGraph Inc).Walk (.inr (D.whiteLabel a)) (.inr (D.whiteLabel (R.face a))) :=
  .cons (v := .inl (D.blackLabel a)) (by exact D.incident a) (.cons (by
    change Inc (D.blackLabel a) (D.whiteLabel (R.white (R.black a)))
    rw [D.whiteLabel_rot, ← D.blackLabel_rot a]
    exact D.incident (R.black a)) .nil)

lemma NoncommBalanced.halfStep_length (D : NoncommBalanced R Inc ι) (a : α) :
    (D.halfStep a).length = 2 := rfl

def NoncommBalanced.boundary (D : NoncommBalanced R Inc ι) (a : α) : (n : ℕ) →
    (incidenceGraph Inc).Walk (.inr (D.whiteLabel a))
      (.inr (D.whiteLabel ((R.face ^ n) a)))
  | 0 => .nil
  | n + 1 => (D.halfStep a).append ((D.boundary (R.face a) n).copy rfl (by
      simp only [pow_succ, Perm.mul_apply]))

lemma NoncommBalanced.boundary_length (D : NoncommBalanced R Inc ι) (a : α) (n : ℕ) :
    (D.boundary a n).length = 2 * n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [NoncommBalanced.boundary, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_copy, NoncommBalanced.halfStep_length, ih]
    omega

lemma NoncommBalanced.boundary_getVert_even (D : NoncommBalanced R Inc ι) (n k : ℕ) (hk : k ≤ n)
    (a : α) : (D.boundary a n).getVert (2 * k) =
      .inr (D.whiteLabel ((R.face ^ k) a)) := by
  induction n generalizing a k with
  | zero => have : k = 0 := Nat.le_zero.mp hk
            subst k
            rfl
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [NoncommBalanced.boundary, SimpleGraph.Walk.getVert_append]
      rw [ite_eq_right (by simp only [NoncommBalanced.halfStep_length]; omega),
        SimpleGraph.Walk.getVert_copy, NoncommBalanced.halfStep_length]
      have heq : 2 * (k + 1) - 2 = 2 * k := by omega
      rw [heq, ih k (by omega)]
      simp only [pow_succ, Perm.mul_apply]

lemma NoncommBalanced.boundary_getVert_odd (D : NoncommBalanced R Inc ι) (n k : ℕ) (hk : k < n)
    (a : α) : (D.boundary a n).getVert (2 * k + 1) =
      .inl (D.blackLabel ((R.face ^ k) a)) := by
  induction n generalizing a k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [NoncommBalanced.boundary, SimpleGraph.Walk.getVert_append]
      rw [ite_eq_right (by simp only [NoncommBalanced.halfStep_length]; omega),
        SimpleGraph.Walk.getVert_copy, NoncommBalanced.halfStep_length]
      have heq : 2 * (k + 1) + 1 - 2 = 2 * k + 1 := by omega
      rw [heq, ih k (by omega)]
      simp only [pow_succ, Perm.mul_apply]

omit [Fintype α] in
lemma cycleClass_pow (p : Perm α) (a : α) (n : ℕ) :
    cycleClass p ((p ^ n) a) = cycleClass p a :=
  (cycleClass_eq _ _ _).mpr ((SameCycle.refl p a).pow_left)

lemma NoncommBalanced.boundary_reduced (D : NoncommBalanced R Inc ι) (hred : D.Reduced)
    (hshort : ShortWords Inc ι) {a : α}
    (ha : cycleClass R.face a ≠ D.exceptionFace) (n : ℕ) :
    _root_.OAI.SimpleGraph.Walk.Reduced (D.boundary a n) := by
  apply SimpleGraph.Walk.reduced_of_getVert
  intro i hi
  rw [D.boundary_length] at hi
  have he : i = 2 * (i / 2) ∨ i = 2 * (i / 2) + 1 := by omega
  rcases he with he | he
  · rw [he, D.boundary_getVert_even n (i / 2) (by omega)]
    have hk : 2 * (i / 2) + 2 = 2 * (i / 2 + 1) := by omega
    rw [hk, D.boundary_getVert_even n (i / 2 + 1) (by omega)]
    intro h
    have hh := Sum.inr.inj h
    rw [pow_succ', Perm.mul_apply] at hh
    change D.whiteLabel ((R.face ^ (i / 2)) a) =
      D.whiteLabel (R.white (R.black ((R.face ^ (i / 2)) a))) at hh
    rw [D.whiteLabel_rot] at hh
    exact hred.2.1 _ (D.black_not_fixed_on_other_face hred hshort (by rwa [cycleClass_pow])) hh.symm
  · rw [he, D.boundary_getVert_odd n (i / 2) (by omega)]
    have hk : 2 * (i / 2) + 1 + 2 = 2 * (i / 2 + 1) + 1 := by omega
    rw [hk, D.boundary_getVert_odd n (i / 2 + 1) (by omega)]
    intro h
    have hh := Sum.inl.inj h
    rw [pow_succ', Perm.mul_apply] at hh
    change D.blackLabel ((R.face ^ (i / 2)) a) =
      D.blackLabel (R.white (R.black ((R.face ^ (i / 2)) a))) at hh
    have hn : R.white (R.black ((R.face ^ (i / 2)) a)) ≠
        R.black ((R.face ^ (i / 2)) a) :=
      D.white_not_fixed hred.1 _
    exact hred.2.2 _ hn (hh.symm.trans (D.blackLabel_rot _).symm)

lemma NoncommBalanced.face_degree (D : NoncommBalanced R Inc ι) (hred : D.Reduced)
    (hshort : ShortWords Inc ι)
    (hgirth : 8 ≤ (incidenceGraph Inc).egirth) (c : Cycles R.face) :
    4 ≤ (cycleSet R.face c).card + if c = D.exceptionFace then 4 else 0 := by
  classical
  by_cases hc : c = D.exceptionFace
  · rw [ite_eq_left hc]; omega
  rw [ite_eq_right hc, add_zero]
  obtain ⟨a, ha⟩ := cycleSet_nonempty R.face c
  have hac : cycleClass R.face a = c := (mem_cycleSet _ _ _).mp ha
  let n := (cycleSet R.face c).card
  have hpa : (R.face ^ n) a = a := by
    change (R.face ^ (cycleSet R.face c).card) a = a
    rw [← hac]
    exact cycleSet_card_pow R.face a
  let p : (incidenceGraph Inc).Walk (.inr (D.whiteLabel a)) (.inr (D.whiteLabel a)) :=
    (D.boundary a n).copy rfl (by rw [hpa])
  have hp : _root_.OAI.SimpleGraph.Walk.Reduced p := by
    exact (D.boundary_reduced hred hshort (by rwa [hac]) n).copy _ _
  have hlen : p.length = 2 * n := by simp only [p, SimpleGraph.Walk.length_copy,
    D.boundary_length]
  have hne : ¬ p.Nil := by
    intro h
    have := SimpleGraph.Walk.Nil.length_eq_zero h
    have hn : 0 < n := (cycleSet_nonempty R.face c).card_pos
    omega
  have hg := hgirth.trans (hp.egirth_le hne)
  rw [hlen] at hg
  have hnat : 8 ≤ 2 * n := by exact_mod_cast hg
  change 4 ≤ n
  omega

theorem NoncommBalanced.reduced_not_genusZero (D : NoncommBalanced R Inc ι)
    (hred : D.Reduced) (hshort : ShortWords Inc ι)
    (hgirth : 8 ≤ (incidenceGraph Inc).egirth) : ¬ R.GenusZero := by
  classical
  intro hR
  have hb := D.black_degree hred hshort
  have hw := D.white_degree hred
  have hf := D.face_degree hred hshort hgirth
  have hb' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.black))) => hb c)
  have hw' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.white))) => hw c)
  have hf' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.face))) => hf c)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, cycles_sum_card] at hw'
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.sum_add_distrib,
    cycles_sum_card, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hb' hf'
  have hc : 0 < Nat.card (Quotient R.components) := by
    have : Nonempty (Quotient R.components) := ⟨Quotient.mk _ D.exception⟩
    exact Nat.card_pos
  unfold Ribbon.GenusZero at hR
  simp only [Nat.card_eq_fintype_card] at hR hc
  omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm OddKaplansky.Holonomy
universe u
variable {α : Type u} {V : Type portUniverse41} {F : Type portUniverse42} {A : Type portUniverse43} {B : Type portUniverse44} [Fintype α] [CommGroup A] [Group B]
variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

def NoncommBalanced.spliceRestrict (D : NoncommBalanced R Inc ι) (a b : α)
    (hl : D.blackLabel a = D.blackLabel b) (P : α → Prop)
    (hb : ∀ x, P ((R.swapBlack a b).black x) ↔ P x)
    (hw : ∀ x, P (R.white x) ↔ P x)
    (E : Defect ((R.swapBlack a b).black.subtypePerm hb) (fun x => D.localWeight x.val)) :
    NoncommBalanced ((R.swapBlack a b).restrict P hb hw) Inc ι where
  blackLabel x := D.blackLabel x.val
  whiteLabel x := D.whiteLabel x.val
  blackLabel_rot x := by
    change D.blackLabel (swap a b (R.black x.val)) = D.blackLabel x.val
    rw [label_swap D.blackLabel a b hl, D.blackLabel_rot]
  whiteLabel_rot x := D.whiteLabel_rot x.val
  incident x := D.incident x.val
  weight x := D.weight x.val
  white_prod c := by
    dsimp only [Ribbon.restrict, Ribbon.swapBlack] at c ⊢
    rw [prod_cycle_subtype R.white P hw c D.weight]
    exact D.white_prod _
  potential := E.potential
  exception := E.exception
  black_balance := E.balance
  black_defect := E.defective

lemma NoncommBalanced.exists_smaller_of_split (D : NoncommBalanced R Inc ι) (a b : α)
    (hl : D.blackLabel a = D.blackLabel b)
    (hS : (R.swapBlack a b).GenusZero)
    (hsep : ¬ (R.swapBlack a b).components.r a b)
    (hne : D.potential a ≠ D.potential b) :
    ∃ (β : Type u) (iβ : Fintype β) (S : Ribbon β),
      @Fintype.card β iβ < Fintype.card α ∧ @Ribbon.GenusZero β iβ S ∧
        Nonempty (@NoncommBalanced β V F A B iβ _ _ S Inc ι) := by
  classical
  have side (a b : α) (hl : D.blackLabel a = D.blackLabel b)
      (hS : (R.swapBlack a b).GenusZero)
      (hab : ¬ (R.swapBlack a b).components.r b a)
      (he : ¬ (R.swapBlack a b).components.r D.exception a)
      (hne : D.potential a ≠ D.potential b) :
      ∃ (β : Type u) (iβ : Fintype β) (S : Ribbon β),
        @Fintype.card β iβ < Fintype.card α ∧ @Ribbon.GenusZero β iβ S ∧
          Nonempty (@NoncommBalanced β V F A B iβ _ _ S Inc ι) := by
    let S := R.swapBlack a b
    let P := fun x => S.components.r x a
    let hb := S.black_component_invariant a
    let hw := S.white_component_invariant a
    let E := D.defect.splitRestrict a b hne P hb (S.components.iseqv.refl a) hab he
    refine ⟨{x // P x}, _, S.restrict P hb hw, ?_, S.planar_restrict hS P hb hw, ?_⟩
    · exact Fintype.card_subtype_lt (x := b) hab
    · exact ⟨D.spliceRestrict a b hl P hb hw E⟩
  have hswap : R.swapBlack b a = R.swapBlack a b := by
    simp only [Ribbon.swapBlack, swap_comm]
  by_cases he : (R.swapBlack a b).components.r D.exception a
  · apply side b a hl.symm
    · rwa [hswap]
    · rwa [hswap]
    · intro hb
      have hb' : (R.swapBlack a b).components.r D.exception b := by
        rwa [hswap] at hb
      exact hsep ((R.swapBlack a b).components.iseqv.trans
        ((R.swapBlack a b).components.iseqv.symm he) hb')
    · exact Ne.symm hne
  · exact side a b hl hS (fun h => hsep ((R.swapBlack a b).components.iseqv.symm h)) he hne

def NoncommBalanced.Minimal (_D : NoncommBalanced R Inc ι) : Prop :=
  ∀ (β : Type u) (iβ : Fintype β) (S : Ribbon β), @Ribbon.GenusZero β iβ S →
    Nonempty (@NoncommBalanced β V F A B iβ _ _ S Inc ι) →
    Fintype.card α ≤ @Fintype.card β iβ

lemma NoncommBalanced.minimal_no_one (D : NoncommBalanced R Inc ι) (hR : R.GenusZero)
    (hm : D.Minimal) (a : α) : D.weight a ≠ 1 := by
  intro ha
  obtain ⟨β, iβ, S, hc, hS, hD⟩ := D.exists_smaller hR a ha
  exact (not_lt_of_ge (hm β iβ S hS hD)) hc

lemma NoncommBalanced.minimal_black_reduced (D : NoncommBalanced R Inc ι)
    (hR : R.GenusZero) (hm : D.Minimal) (a : α) (ha : R.black a ≠ a) :
    D.whiteLabel (R.black a) ≠ D.whiteLabel a := by
  intro hl
  by_cases hw : R.white.SameCycle a (R.black a)
  · let E := D.combine a (R.black a) ha.symm rfl hw
    have hEm : E.Minimal := hm
    exact E.minimal_no_one hR hEm a (by simp [E, NoncommBalanced.combine,
      NoncommBalanced.withDefect, combineWeight])
  · let E := D.mergeWhite a hw hl
    have hER := R.genusZero_mergeWhite hR a hw
    have hab : (R.mergeWhite a).white.SameCycle a (R.black a) := by
      have h := swap_mul_sameCycle R.white a (R.face a) (by simpa [Ribbon.face] using hw)
      exact h.trans ((sameCycle_swap_mul R.white a (R.face a)
        (by simpa [Ribbon.face] using hw)) ((SameCycle.refl R.white (R.black a)).apply_left))
    let E' := E.combine a (R.black a) ha.symm rfl hab
    have hEm : E'.Minimal := hm
    exact E'.minimal_no_one hER hEm a (by simp [E', NoncommBalanced.combine,
      NoncommBalanced.withDefect, combineWeight])

lemma NoncommBalanced.minimal_white_reduced (D : NoncommBalanced R Inc ι)
    (hR : R.GenusZero) (hm : D.Minimal) (a : α) (ha : R.white a ≠ a) :
    D.blackLabel (R.white a) ≠ D.blackLabel a := by
  classical
  intro hl
  let b := R.white a
  have hba : b ≠ a := ha
  have hw : R.white.SameCycle b a := (SameCycle.refl R.white a).apply_left
  by_cases hp : R.black b = a
  · let E := D.combine b a hba hp hw
    have hEm : E.Minimal := hm
    exact E.minimal_no_one hR hEm b (by simp [E, NoncommBalanced.combine,
      NoncommBalanced.withDefect, combineWeight])
  have hl' : D.blackLabel a = D.blackLabel (R.black b) := by rw [D.blackLabel_rot, hl]
  have hpa : a ≠ R.black b := Ne.symm hp
  have finish (E : Holonomy.Defect (swap a (R.black b) * R.black) D.localWeight)
      (hS : (R.swapBlack a (R.black b)).GenusZero) : False := by
    let D' := D.spliceBlack a (R.black b) hl' E
    have hrot : (R.swapBlack a (R.black b)).black b = a := by simp [Ribbon.swapBlack]
    let D'' := D'.combine b a hba hrot hw
    have hDm : D''.Minimal := hm
    exact D''.minimal_no_one hS hDm b (by simp [D'', NoncommBalanced.combine,
      NoncommBalanced.withDefect, combineWeight])
  by_cases hs : R.black.SameCycle a (R.black b)
  · have hS := R.genusZero_swapBlack_split hR a (R.black b) hpa hs
    by_cases ht : D.potential a = D.potential (R.black b)
    · exact finish (D.defect.swapEqual a (R.black b) ht) hS
    · have hsep := R.mergeBlack_separates hR a hpa hs
      obtain ⟨β, iβ, S, hc, hS', hD⟩ := D.exists_smaller_of_split a (R.black b) hl' hS hsep ht
      exact (not_lt_of_ge (hm β iβ S hS' hD)) hc
  · have hS : (R.swapBlack a (R.black b)).GenusZero :=
      R.genusZero_mergeBlack hR a (by simpa only [sameCycle_apply_right] using hs)
    exact finish (D.defect.merge a (R.black b) hs) hS

lemma NoncommBalanced.minimal_reduced (D : NoncommBalanced R Inc ι)
    (hR : R.GenusZero) (hm : D.Minimal) : D.Reduced :=
  ⟨D.minimal_no_one hR hm, D.minimal_black_reduced hR hm, D.minimal_white_reduced hR hm⟩

theorem NoncommBalanced.not_genusZero (D : NoncommBalanced R Inc ι)
    (hshort : ShortWords Inc ι) (hgirth : 8 ≤ (incidenceGraph Inc).egirth) :
    ¬ R.GenusZero := by
  intro hR
  let P : ℕ → Prop := fun n => ∃ (β : Type u) (iβ : Fintype β) (S : Ribbon β),
    @Fintype.card β iβ = n ∧ @Ribbon.GenusZero β iβ S ∧
      Nonempty (@NoncommBalanced β V F A B iβ _ _ S Inc ι)
  have hex : ∃ n, P n := ⟨Fintype.card α, α, inferInstance, R, rfl, hR, ⟨D⟩⟩
  classical
  obtain ⟨β, iβ, S, hcard, hS, ⟨E⟩⟩ := Nat.find_spec hex
  let := iβ
  have hm : E.Minimal := by
    intro γ iγ T hT hE
    rw [hcard]
    exact Nat.find_min' hex ⟨γ, iγ, T, rfl, hT, hE⟩
  exact E.reduced_not_genusZero (E.minimal_reduced hS hm) hshort hgirth hS

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse45} {β : Type portUniverse46}

def sumSetoid (s : Setoid α) (t : Setoid β) : Setoid (α ⊕ β) :=
  Setoid.ker (Sum.map (Quotient.mk s) (Quotient.mk t))

@[simp] lemma sumSetoid_inl (s : Setoid α) (t : Setoid β) (x y : α) :
    (sumSetoid s t).r (.inl x) (.inl y) ↔ s.r x y := by
  change (Sum.inl (Quotient.mk s x) : Quotient s ⊕ Quotient t) = .inl (Quotient.mk s y) ↔ _
  simp only [Sum.inl.injEq, Quotient.eq]

@[simp] lemma sumSetoid_inr (s : Setoid α) (t : Setoid β) (x y : β) :
    (sumSetoid s t).r (.inr x) (.inr y) ↔ t.r x y := by
  change (Sum.inr (Quotient.mk t x) : Quotient s ⊕ Quotient t) = .inr (Quotient.mk t y) ↔ _
  simp only [Sum.inr.injEq, Quotient.eq]

@[simp] lemma sumSetoid_cross (s : Setoid α) (t : Setoid β) (x : α) (y : β) :
    ¬ (sumSetoid s t).r (.inl x) (.inr y) := by
  change ¬ (Sum.inl (Quotient.mk s x) : Quotient s ⊕ Quotient t) = .inr (Quotient.mk t y)
  simp

def sumSetoidEquiv (s : Setoid α) (t : Setoid β) :
    Quotient (sumSetoid s t) ≃ Quotient s ⊕ Quotient t :=
  Setoid.quotientKerEquivOfSurjective (Sum.map (Quotient.mk s) (Quotient.mk t)) (by
    rintro (x | y)
    · induction x using Quotient.inductionOn with
      | h x => exact ⟨.inl x, rfl⟩
    · induction y using Quotient.inductionOn with
      | h y => exact ⟨.inr y, rfl⟩)

lemma sumSetoid_card [Fintype α] [Fintype β] (s : Setoid α) (t : Setoid β) :
    Nat.card (Quotient (sumSetoid s t)) = Nat.card (Quotient s) + Nat.card (Quotient t) := by
  rw [Nat.card_congr (sumSetoidEquiv s t), Nat.card_sum]

lemma sumSetoid_le {s : Setoid α} {t : Setoid β} {r : Setoid (α ⊕ β)}
    (hl : ∀ x y, s.r x y → r.r (.inl x) (.inl y))
    (hr : ∀ x y, t.r x y → r.r (.inr x) (.inr y)) : sumSetoid s t ≤ r := by
  rintro (x | x) (y | y) h
  · exact hl x y ((sumSetoid_inl _ _ _ _).mp h)
  · exact False.elim (sumSetoid_cross _ _ _ _ h)
  · exact False.elim (sumSetoid_cross _ _ _ _ ((sumSetoid s t).iseqv.symm h))
  · exact hr x y ((sumSetoid_inr _ _ _ _).mp h)

variable [Fintype α] [Fintype β]

lemma sumCongr_cycles_setoid (p : Perm α) (q : Perm β) :
    SameCycle.setoid (Equiv.sumCongr p q) = sumSetoid (SameCycle.setoid p) (SameCycle.setoid q) := by
  apply le_antisymm
  · intro x y h
    apply setoid_sameCycle_of_step _ (Equiv.sumCongr p q) _ h
    rintro (z | z) <;> simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      sumSetoid_inl, sumSetoid_inr]
    · exact SameCycle.apply_right SameCycle.rfl
    · exact SameCycle.apply_right SameCycle.rfl
  · apply sumSetoid_le
    · intro x y h
      exact sameCycle_map p (Equiv.sumCongr p q) Sum.inl
        (fun z => SameCycle.apply_right SameCycle.rfl) h
    · intro x y h
      exact sameCycle_map q (Equiv.sumCongr p q) Sum.inr
        (fun z => SameCycle.apply_right SameCycle.rfl) h

lemma sumCongr_cycles_card (p : Perm α) (q : Perm β) :
    Nat.card (Cycles (Equiv.sumCongr p q)) = Nat.card (Cycles p) + Nat.card (Cycles q) := by
  rw [Cycles, sumCongr_cycles_setoid]
  exact sumSetoid_card _ _

def Ribbon.sum (R : Ribbon α) (S : Ribbon β) : Ribbon (α ⊕ β) :=
  ⟨Equiv.sumCongr R.black S.black, Equiv.sumCongr R.white S.white⟩

omit [Fintype α] [Fintype β] in
lemma Ribbon.sum_face (R : Ribbon α) (S : Ribbon β) :
    (R.sum S).face = Equiv.sumCongr R.face S.face := by
  ext x
  cases x <;> rfl

lemma Ribbon.sum_components (R : Ribbon α) (S : Ribbon β) :
    (R.sum S).components = sumSetoid R.components S.components := by
  apply le_antisymm
  · apply (R.sum S).components_le_of_steps
    · rintro (x | x)
      · exact (sumSetoid_inl _ _ _ _).mpr (R.black_step x)
      · exact (sumSetoid_inr _ _ _ _).mpr (S.black_step x)
    · rintro (x | x)
      · exact (sumSetoid_inl _ _ _ _).mpr (R.white_step x)
      · exact (sumSetoid_inr _ _ _ _).mpr (S.white_step x)
  · apply sumSetoid_le
    · have h := R.components_le_of_steps ((R.sum S).components.comap Sum.inl)
        (fun x => (R.sum S).black_step (.inl x))
        (fun x => (R.sum S).white_step (.inl x))
      exact fun x y hxy => h hxy
    · have h := S.components_le_of_steps ((R.sum S).components.comap Sum.inr)
        (fun x => (R.sum S).black_step (.inr x))
        (fun x => (R.sum S).white_step (.inr x))
      exact fun x y hxy => h hxy

lemma Ribbon.genusZero_sum (R : Ribbon α) (S : Ribbon β)
    (hR : R.GenusZero) (hS : S.GenusZero) : (R.sum S).GenusZero := by
  unfold Ribbon.GenusZero at *
  rw [R.sum_face, R.sum_components, sumSetoid_card, Fintype.card_sum]
  change Nat.card (Cycles (Equiv.sumCongr R.black S.black)) +
    Nat.card (Cycles (Equiv.sumCongr R.white S.white)) + _ = _
  rw [sumCongr_cycles_card, sumCongr_cycles_card, sumCongr_cycles_card]
  omega

omit [Fintype α] [Fintype β] in
lemma formPerm_append_nonempty [DecidableEq α] (a b : α) (l m : List α)
    (hb : b ∉ a :: l) :
    ((a :: l) ++ (b :: m)).formPerm = swap a b * (a :: l).formPerm * (b :: m).formPerm := by
  induction l generalizing a with
  | nil => simp
  | cons c l ih =>
    have hba : b ≠ a := fun h => hb (by simp [h])
    have hbc : b ≠ c := fun h => hb (by simp [h])
    have hc : b ∉ c :: l := fun h => hb (List.mem_cons_of_mem _ h)
    have hs : swap a c * swap c b = swap a b * swap a c := by
      rw [mul_swap_eq_swap_mul]
      simp [swap_apply_of_ne_of_ne hba hbc]
    simp only [List.cons_append, List.formPerm_cons_cons]
    rw [show c :: (l ++ b :: m) = (c :: l) ++ (b :: m) from rfl, ih c hc]
    simp only [← mul_assoc, hs]

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse47} [Fintype α]

def Ribbon.wheel (p : Perm α) : Ribbon (α ⊕ α) :=
  ⟨Equiv.sumCongr p p⁻¹, Equiv.sumComm α α⟩

def sumIndex : α ⊕ α → α := Sum.elim id id

def wheelFaceIndex (p : Perm α) : α ⊕ α → α := Sum.elim id (fun x => p⁻¹ x)

omit [Fintype α] in
@[simp] lemma wheel_white_index (p : Perm α) (x : α ⊕ α) :
    sumIndex ((Ribbon.wheel p).white x) = sumIndex x := by cases x <;> rfl

omit [Fintype α] in
@[simp] lemma wheel_face_index (p : Perm α) (x : α ⊕ α) :
    wheelFaceIndex p ((Ribbon.wheel p).face x) = wheelFaceIndex p x := by
  cases x <;> simp [Ribbon.wheel, Ribbon.face, wheelFaceIndex]

lemma wheel_white_setoid (p : Perm α) :
    SameCycle.setoid (Ribbon.wheel p).white = Setoid.ker sumIndex := by
  apply le_antisymm
  · intro x y h
    apply setoid_sameCycle_of_step _ (Ribbon.wheel p).white _ h
    exact fun z => (wheel_white_index p z).symm
  · rintro (x | x) (y | y) h <;> change x = y at h <;> subst y
    · exact SameCycle.rfl
    · exact SameCycle.apply_right SameCycle.rfl
    · exact SameCycle.apply_right SameCycle.rfl
    · exact SameCycle.rfl

lemma wheel_face_setoid (p : Perm α) :
    SameCycle.setoid (Ribbon.wheel p).face = Setoid.ker (wheelFaceIndex p) := by
  apply le_antisymm
  · intro x y h
    apply setoid_sameCycle_of_step _ (Ribbon.wheel p).face _ h
    exact fun z => (wheel_face_index p z).symm
  · rintro (x | x) (y | y) h
    · change x = y at h
      subst y
      exact SameCycle.rfl
    · change x = p⁻¹ y at h
      subst x
      change (Ribbon.wheel p).face.SameCycle (.inl (p⁻¹ y)) (.inr y)
      convert (SameCycle.apply_right
        (SameCycle.rfl (f := (Ribbon.wheel p).face) (x := Sum.inl (p⁻¹ y)))) using 1
      simp [Ribbon.wheel, Ribbon.face]
    · change p⁻¹ x = y at h
      subst y
      exact SameCycle.apply_right SameCycle.rfl
    · change p⁻¹ x = p⁻¹ y at h
      have := p.symm.injective h
      subst y
      exact SameCycle.rfl

lemma wheel_component_index (p : Perm α) :
    (Ribbon.wheel p).components = Setoid.ker (cycleClass p ∘ sumIndex) := by
  let R := Ribbon.wheel p
  apply le_antisymm
  · apply R.components_le_of_steps
    · rintro (x | x)
      · exact (cycleClass_apply p x).symm
      · change cycleClass p x = cycleClass p (p⁻¹ x)
        exact (cycleClass_eq _ _ _).mpr (by simp [SameCycle.rfl])
    · intro x
      change cycleClass p (sumIndex x) = cycleClass p (sumIndex (R.white x))
      rw [wheel_white_index]
  · intro x y h
    have hx : R.components.r x (.inl (sumIndex x)) := by
      cases x with
      | inl x => exact R.components.iseqv.refl _
      | inr x => exact R.white_step (.inr x)
    have hy : R.components.r y (.inl (sumIndex y)) := by
      cases y with
      | inl y => exact R.components.iseqv.refl _
      | inr y => exact R.white_step (.inr y)
    have hxy : p.SameCycle (sumIndex x) (sumIndex y) := (cycleClass_eq _ _ _).mp h
    have hp : R.black.SameCycle (.inl (sumIndex x)) (.inl (sumIndex y)) :=
      sameCycle_map p R.black Sum.inl (fun z => SameCycle.apply_right SameCycle.rfl) hxy
    exact R.components.iseqv.trans hx (R.components.iseqv.trans
      ((show SameCycle.setoid R.black ≤ R.components from le_sup_left) hp)
      (R.components.iseqv.symm hy))

lemma wheel_white_card (p : Perm α) :
    Nat.card (Cycles (Ribbon.wheel p).white) = Fintype.card α := by
  rw [Cycles, wheel_white_setoid]
  exact (Nat.card_congr (Setoid.quotientKerEquivOfSurjective sumIndex
    (fun x => ⟨.inl x, rfl⟩))).trans Nat.card_eq_fintype_card

lemma wheel_face_card (p : Perm α) :
    Nat.card (Cycles (Ribbon.wheel p).face) = Fintype.card α := by
  rw [Cycles, wheel_face_setoid]
  exact (Nat.card_congr (Setoid.quotientKerEquivOfSurjective (wheelFaceIndex p)
    (fun x => ⟨.inl x, rfl⟩))).trans Nat.card_eq_fintype_card

lemma wheel_component_card (p : Perm α) :
    Nat.card (Quotient (Ribbon.wheel p).components) = Nat.card (Cycles p) := by
  rw [wheel_component_index]
  apply Nat.card_congr
  apply Setoid.quotientKerEquivOfSurjective
  intro c
  induction c using Quotient.inductionOn with
  | h x => exact ⟨.inl x, rfl⟩

lemma Ribbon.genusZero_wheel (p : Perm α) : (Ribbon.wheel p).GenusZero := by
  unfold Ribbon.GenusZero
  rw [wheel_white_card, wheel_face_card, wheel_component_card, Fintype.card_sum]
  change Nat.card (Cycles (Equiv.sumCongr p p⁻¹)) + _ + _ = _
  rw [sumCongr_cycles_card, cycles_inv_card]
  omega

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse48} {β : Type portUniverse49} {A : Type portUniverse50} [Fintype α]

def Follows (p : Perm α) (l : List α) : Prop := ∀ x ∈ l, p x = l.formPerm x

omit [Fintype α] in
lemma Follows.invariant {p : Perm α} {l : List α} (h : Follows p l) (x : α) :
    p x ∈ l ↔ x ∈ l := by
  classical
  constructor
  · intro hx
    let y := l.formPerm⁻¹ (p x)
    have hy : y ∈ l := by
      apply l.mem_of_formPerm_apply_mem
      simpa [y] using hx
    have he : p y = p x := by rw [h y hy]; simp [y]
    simpa [p.injective he] using hy
  · intro hx
    rw [h x hx]
    exact l.formPerm_apply_mem_of_mem hx

lemma Follows.sameCycle {p : Perm α} {l : List α} (h : Follows p l)
    (hd : l.Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) : p.SameCycle x y := by
  apply sameCycle_map l.formPerm p id _ (hd.isCycleOn_formPerm.2 hx hy)
  intro z
  by_cases hz : z ∈ l
  · change p.SameCycle z (l.formPerm z)
    rw [← h z hz]
    exact SameCycle.apply_right SameCycle.rfl
  · simp only [id_eq, List.formPerm_apply_of_notMem hz]
    exact SameCycle.rfl

lemma Follows.cycleSet {p : Perm α} {l : List α} (h : Follows p l)
    (hd : l.Nodup) {x : α} (hx : x ∈ l) :
    cycleSet p (cycleClass p x) = l.toFinset := by
  classical
  ext y
  rw [mem_cycleSet, cycleClass_eq, List.mem_toFinset]
  constructor
  · intro hy
    exact (perm_invariant_cycle p (fun z => z ∈ l) h.invariant hy).mpr hx
  · exact fun hy => h.sameCycle hd hy hx

lemma sameCycle_iff_of_eqOn_cycle (p q : Perm α) (x : α)
    (heq : ∀ z, p.SameCycle x z → q z = p z) (y : α) :
    q.SameCycle x y ↔ p.SameCycle x y := by
  have hp : ∀ n : ℕ, (q ^ n) x = (p ^ n) x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, ih]
      exact heq _ (by simp [SameCycle.rfl])
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [hp] at hn
    exact ⟨n, by simpa using hn⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by simpa [hp n] using hn⟩

lemma cycleSet_eq_of_eqOn_cycle (p q : Perm α) (x : α)
    (heq : ∀ z, p.SameCycle x z → q z = p z) :
    cycleSet q (cycleClass q x) = cycleSet p (cycleClass p x) := by
  ext y
  simp only [mem_cycleSet, cycleClass_eq, sameCycle_comm (x := y)]
  exact sameCycle_iff_of_eqOn_cycle p q x heq y

omit [Fintype α] in
lemma formPerm_map_apply [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (l : List α) (x : α) :
    (l.map f).formPerm (f x) = f (l.formPerm x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      change swap (f a) (f b) (((b :: l).map f).formPerm (f x)) =
        f (swap a b ((b :: l).formPerm x))
      rw [ih]
      exact (hf.map_swap a b _).symm

omit [Fintype α] in
lemma Follows.map_sum_left {p : Perm α} {q : Perm β} {l : List α}
    (h : Follows p l) : Follows (Equiv.sumCongr p q) (l.map Sum.inl) := by
  classical
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simpa only [Equiv.sumCongr_apply, Sum.map_inl,
    formPerm_map_apply Sum.inl Sum.inl_injective] using congrArg Sum.inl (h x hx)

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse51} {β : Type portUniverse52} {A : Type portUniverse53} [Fintype α] [Fintype β] [CommGroup A]

@[simp] lemma sumCongr_sameCycle_inl (p : Perm α) (q : Perm β) (x y : α) :
    SameCycle (Equiv.sumCongr p q) (.inl x) (.inl y) ↔ p.SameCycle x y := by
  change (SameCycle.setoid (Equiv.sumCongr p q)).r _ _ ↔ _
  rw [sumCongr_cycles_setoid]
  exact sumSetoid_inl _ _ _ _

@[simp] lemma sumCongr_sameCycle_inr (p : Perm α) (q : Perm β) (x y : β) :
    SameCycle (Equiv.sumCongr p q) (.inr x) (.inr y) ↔ q.SameCycle x y := by
  change (SameCycle.setoid (Equiv.sumCongr p q)).r _ _ ↔ _
  rw [sumCongr_cycles_setoid]
  exact sumSetoid_inr _ _ _ _

@[simp] lemma sumCongr_not_sameCycle (p : Perm α) (q : Perm β) (x : α) (y : β) :
    ¬ SameCycle (Equiv.sumCongr p q) (.inl x) (.inr y) := by
  change ¬ (SameCycle.setoid (Equiv.sumCongr p q)).r _ _
  rw [sumCongr_cycles_setoid]
  exact sumSetoid_cross _ _ _ _

lemma prod_cycle_sum_left (p : Perm α) (q : Perm β) (x : α) (f : α ⊕ β → A) :
    ∏ y ∈ cycleSet (Equiv.sumCongr p q) (cycleClass _ (.inl x)), f y =
      ∏ y ∈ cycleSet p (cycleClass p x), f (.inl y) := by
  simp only [cycleSet, Finset.prod_filter, cycleClass_eq, Fintype.prod_sum_type,
    sumCongr_sameCycle_inl, sameCycle_comm (x := Sum.inr _), sumCongr_not_sameCycle,
    ↓reduceIte, Finset.prod_const_one, mul_one]

lemma prod_cycle_sum_right (p : Perm α) (q : Perm β) (x : β) (f : α ⊕ β → A) :
    ∏ y ∈ cycleSet (Equiv.sumCongr p q) (cycleClass _ (.inr x)), f y =
      ∏ y ∈ cycleSet q (cycleClass q x), f (.inr y) := by
  simp only [cycleSet, Finset.prod_filter, cycleClass_eq, Fintype.prod_sum_type,
    sumCongr_sameCycle_inr, sumCongr_not_sameCycle,
    ↓reduceIte, Finset.prod_const_one, one_mul]

def cycleInl (p : Perm α) (q : Perm β) : Cycles p → Cycles (Equiv.sumCongr p q) :=
  Quotient.map Sum.inl (fun _ _ h => (sumCongr_sameCycle_inl p q _ _).mpr h)

@[simp] lemma cycleInl_class (p : Perm α) (q : Perm β) (x : α) :
    cycleInl p q (cycleClass p x) = cycleClass _ (.inl x) := rfl

lemma cycleInl_injective (p : Perm α) (q : Perm β) :
    Function.Injective (cycleInl p q) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      change cycleClass (Equiv.sumCongr p q) (.inl x) = cycleClass _ (.inl y) →
        cycleClass p x = cycleClass p y
      simp only [cycleClass_eq, sumCongr_sameCycle_inl, imp_self]

lemma cycleInl_ne_inr (p : Perm α) (q : Perm β) (c : Cycles p) (y : β) :
    cycleInl p q c ≠ cycleClass _ (.inr y) := by
  induction c using Quotient.inductionOn with
  | h x =>
    change cycleClass (Equiv.sumCongr p q) (.inl x) ≠ cycleClass _ (.inr y)
    simp only [ne_eq, cycleClass_eq, sumCongr_not_sameCycle, not_false_eq_true]

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse54}

lemma Follows.append_rotate {p : Perm α} {l m : List α} (h : Follows p (l ++ m))
    (hd : (l ++ m).Nodup) : Follows p (m ++ l) := by
  intro x hx
  have hx' : x ∈ l ++ m := by simpa only [List.mem_append, or_comm] using hx
  rw [h x hx', List.formPerm_eq_of_isRotated hd List.isRotated_append]

lemma Follows.split {p : Perm α} {a b : α} {l m : List α}
    (h : Follows p ((a :: l) ++ (b :: m))) (hd : ((a :: l) ++ (b :: m)).Nodup) :
    Follows (swap a b * p) (a :: l) ∧ Follows (swap a b * p) (b :: m) := by
  classical
  have hdis : List.Disjoint (a :: l) (b :: m) := by
    intro x hx hy
    exact (List.nodup_append.mp hd).2.2 x hx x hy rfl
  have hb : b ∉ a :: l := fun hb => hdis hb (by simp)
  have heq (x : α) (hx : x ∈ (a :: l) ++ (b :: m)) :
      (swap a b * p) x = (a :: l).formPerm ((b :: m).formPerm x) := by
    rw [Perm.mul_apply, h x hx, formPerm_append_nonempty a b l m hb]
    simp only [Perm.mul_apply, swap_apply_self]
  constructor
  · intro x hx
    have hx' : x ∉ b :: m := fun hx' => hdis hx hx'
    rw [heq x (List.mem_append_left _ hx), List.formPerm_apply_of_notMem hx']
  · intro x hx
    rw [heq x (List.mem_append_right _ hx)]
    apply List.formPerm_apply_of_notMem
    exact fun hx' => hdis hx' ((b :: m).formPerm_apply_mem_of_mem hx)

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse55} {β : Type portUniverse56}

lemma Follows.map_sum_right {p : Perm α} {q : Perm β} {l : List β}
    (h : Follows q l) : Follows (Equiv.sumCongr p q) (l.map Sum.inr) := by
  classical
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simpa only [Equiv.sumCongr_apply, Sum.map_inr,
    formPerm_map_apply Sum.inr Sum.inr_injective] using congrArg Sum.inr (h x hx)

lemma Follows.merge {p : Perm α} {a b : α} {l m : List α}
    (hl : Follows p (a :: l)) (hm : Follows p (b :: m))
    (hdis : List.Disjoint (a :: l) (b :: m)) :
    Follows (swap a b * p) ((a :: l) ++ (b :: m)) := by
  classical
  have hb : b ∉ a :: l := fun hb => hdis hb (by simp)
  intro x hx
  rw [formPerm_append_nonempty a b l m hb]
  simp only [Perm.mul_apply]
  apply congrArg (swap a b)
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.formPerm_apply_of_notMem (fun h => hdis hx h)]
    exact hl x hx
  · rw [List.formPerm_apply_of_notMem (fun h => hdis h ((b :: m).formPerm_apply_mem_of_mem hx))]
    exact hm x hx

end OddKaplansky.Planar
namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse57}

lemma follows_formPerm [DecidableEq α] (l : List α) : Follows l.formPerm l := by
  intro x _
  exact congrArg (fun d : DecidableEq α => @List.formPerm α d l x)
    (Subsingleton.elim _ _)

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse58} {B : Type portUniverse59} [Group B]

noncomputable def listPotential [DecidableEq α] (l : List α) (w : α → B) (x : α) : B :=
  ((l.take (l.idxOf x)).map w).prod

lemma listPotential_get [DecidableEq α] (l : List α) (hd : l.Nodup) (w : α → B)
    (i : ℕ) (hi : i < l.length) :
    listPotential l w l[i] = ((l.take i).map w).prod := by
  simp only [listPotential, hd.idxOf_getElem i hi]

lemma listPrefix_succ (l : List α) (w : α → B) (i : ℕ) (hi : i < l.length) :
    ((l.take (i+1)).map w).prod = ((l.take i).map w).prod * w l[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.prod_append,
    List.map_singleton, List.prod_singleton]

lemma listPotential_balance_at [DecidableEq α] (l : List α) (hd : l.Nodup)
    (w : α → B) (i : ℕ) (hi : i + 1 < l.length) :
    listPotential l w (l.formPerm l[i]) = listPotential l w l[i] * w l[i] := by
  rw [List.formPerm_apply_lt_getElem l hd i hi, listPotential_get l hd w (i+1),
    listPotential_get l hd w i, listPrefix_succ]

lemma listPotential_end_at [DecidableEq α] (l : List α) (hd : l.Nodup)
    (w : α → B) (i : ℕ) (hi : i < l.length) (hend : i+1 = l.length) :
    listPotential l w (l.formPerm l[i]) = 1 ∧
      listPotential l w l[i] * w l[i] = (l.map w).prod := by
  constructor
  · rw [List.formPerm_apply_getElem l hd i hi]
    have hm : (i+1) % l.length = 0 := by rw [hend, Nat.mod_self]
    simp only [hm]
    rw [listPotential_get l hd w 0]
    rfl
  · rw [listPotential_get l hd w i, ← listPrefix_succ l w i hi, hend, List.take_length]

lemma listPotential_balance [DecidableEq α] (l : List α) (hd : l.Nodup)
    (w : α → B) (hprod : (l.map w).prod = 1) (x : α) (hx : x ∈ l) :
    listPotential l w (l.formPerm x) = listPotential l w x * w x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  by_cases hn : i+1 < l.length
  · exact listPotential_balance_at l hd w i hn
  · have he := listPotential_end_at l hd w i hi (by omega)
    rw [he.1, he.2, hprod]

def listDefect [Fintype α] [DecidableEq α] (l : List α) (hd : l.Nodup) (hall : ∀ x, x ∈ l)
    (w : α → B) (hprod : (l.map w).prod ≠ 1) : Holonomy.Defect l.formPerm w := by
  have hn : 0 < l.length := by
    by_contra h
    have he : l = [] := List.length_eq_zero_iff.mp (by omega)
    simp [he] at hprod
  let e := l[l.length-1]'(by omega)
  refine ⟨listPotential l w, e, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hall x)
    apply listPotential_balance_at l hd w i
    by_contra h
    have he : i = l.length-1 := by omega
    exact hx (by simp only [he, e])
  · have he := listPotential_end_at l hd w (l.length-1) (by omega) (by omega)
    change listPotential l w (l.formPerm e) ≠ listPotential l w e * w e
    rw [show listPotential l w (l.formPerm e) = 1 from he.1,
      show listPotential l w e * w e = (l.map w).prod from he.2]
    exact Ne.symm hprod

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse60} {β : Type portUniverse61} {V : Type portUniverse62} {F : Type portUniverse63} {A : Type portUniverse64} {B : Type portUniverse65} [Fintype α] [Fintype β] [CommGroup A] [Group B]

def augInc (Inc : V → F → Prop) : Option V → F → Prop
  | none, _ => True
  | some v, f => Inc v f

def augMap (ι : V → F → (A →* B)) : Option V → F → (A →* B)
  | none, _ => 1
  | some v, f => ι v f

structure OpenBalanced (R : Ribbon α) (Inc : V → F → Prop) (ι : V → F → (A →* B))
    extends NoncommBalanced R (augInc Inc) (augMap ι) where
  potential_none : ∀ x, blackLabel x = none → potential x = 1
  exception_some : blackLabel exception ≠ none

structure FlatOpenBalanced (R : Ribbon α) (Inc : V → F → Prop) (ι : V → F → (A →* B)) where
  blackLabel : α → Option V
  whiteLabel : α → F
  blackLabel_rot : ∀ a, blackLabel (R.black a) = blackLabel a
  whiteLabel_rot : ∀ a, whiteLabel (R.white a) = whiteLabel a
  incident : ∀ a, augInc Inc (blackLabel a) (whiteLabel a)
  weight : α → A
  white_prod : ∀ c : Cycles R.white, ∏ a ∈ cycleSet R.white c, weight a = 1
  potential : α → B
  black_balance : ∀ a,
    potential (R.black a) = potential a * augMap ι (blackLabel a) (whiteLabel a) (weight a)
  potential_none : ∀ x, blackLabel x = none → potential x = 1

variable {R : Ribbon α} {S : Ribbon β} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

def OpenBalanced.sumZero (D : OpenBalanced R Inc ι) (E : FlatOpenBalanced S Inc ι) :
    OpenBalanced (R.sum S) Inc ι where
  blackLabel := Sum.elim D.blackLabel E.blackLabel
  whiteLabel := Sum.elim D.whiteLabel E.whiteLabel
  blackLabel_rot := by rintro (x | x); exact D.blackLabel_rot x; exact E.blackLabel_rot x
  whiteLabel_rot := by rintro (x | x); exact D.whiteLabel_rot x; exact E.whiteLabel_rot x
  incident := by rintro (x | x); exact D.incident x; exact E.incident x
  weight := Sum.elim D.weight E.weight
  white_prod c := by
    dsimp only [Ribbon.sum] at c ⊢
    induction c using Quotient.inductionOn with
    | h x =>
      cases x with
      | inl x =>
        change (∏ a ∈ cycleSet (Equiv.sumCongr R.white S.white) (cycleClass _ (.inl x)), Sum.elim D.weight E.weight a) = 1
        rw [prod_cycle_sum_left]
        exact D.white_prod _
      | inr x =>
        change (∏ a ∈ cycleSet (Equiv.sumCongr R.white S.white) (cycleClass _ (.inr x)), Sum.elim D.weight E.weight a) = 1
        rw [prod_cycle_sum_right]
        exact E.white_prod _
  potential := Sum.elim D.potential E.potential
  exception := .inl D.exception
  black_balance := by
    rintro (x | x) hx
    · exact D.black_balance x (fun h => hx (congrArg Sum.inl h))
    · exact E.black_balance x
  black_defect := D.black_defect
  potential_none := by rintro (x | x); exact D.potential_none x; exact E.potential_none x
  exception_some := D.exception_some

def OpenBalanced.joinNone (D : OpenBalanced R Inc ι) (a b : α)
    (ha : D.blackLabel a = none) (hb : D.blackLabel b = none) :
    OpenBalanced (R.swapBlack a b) Inc ι where
  toNoncommBalanced := D.toNoncommBalanced.spliceBlack a b (ha.trans hb.symm)
    (D.toNoncommBalanced.defect.swapEqual a b
      ((D.potential_none a ha).trans (D.potential_none b hb).symm))
  potential_none := D.potential_none
  exception_some := D.exception_some

def OpenBalanced.fill (D : OpenBalanced R Inc ι)
    (l : List α) (hd : l.Nodup) (hrot : Follows R.black l)
    (hnone : ∀ x ∈ l, D.blackLabel x = none) (v : V)
    (hinc : ∀ x ∈ l, Inc v (D.whiteLabel x))
    (hprod : (l.map fun x => ι v (D.whiteLabel x) (D.weight x)).prod = 1) :
    OpenBalanced R Inc ι := by
  classical
  let w := fun x => ι v (D.whiteLabel x) (D.weight x)
  have he : D.exception ∉ l := fun h => D.exception_some (hnone _ h)
  have hep : R.black D.exception ∉ l := by simpa only [hrot.invariant] using he
  refine {
    blackLabel := fun x => if x ∈ l then some v else D.blackLabel x
    whiteLabel := D.whiteLabel
    blackLabel_rot := ?_
    whiteLabel_rot := D.whiteLabel_rot
    incident := ?_
    weight := D.weight
    white_prod := D.white_prod
    potential := fun x => if x ∈ l then listPotential l w x else D.potential x
    exception := D.exception
    black_balance := ?_
    black_defect := ?_
    potential_none := ?_
    exception_some := ?_ }
  · intro x; simp only [hrot.invariant, D.blackLabel_rot]
  · intro x
    by_cases hx : x ∈ l
    · simpa only [ite_eq_left hx, augInc] using hinc x hx
    · simpa only [ite_eq_right hx] using D.incident x
  · intro x hx
    by_cases hxl : x ∈ l
    · simp only [hrot.invariant, hxl, ite_true, augMap]
      rw [hrot x hxl]
      exact listPotential_balance l hd w hprod x hxl
    · simp only [hrot.invariant, hxl, ite_false]
      exact D.black_balance x hx
  · simpa only [ite_eq_right he, ite_eq_right hep] using D.black_defect
  · intro x hx
    by_cases hxl : x ∈ l
    · simp only [ite_eq_left hxl] at hx
      exact (Option.some_ne_none v hx).elim
    · simp only [ite_eq_right hxl] at hx ⊢
      exact D.potential_none x hx
  · simpa only [ite_eq_right he] using D.exception_some

structure OpenDiagram (Inc : V → F → Prop) (ι : V → F → (A →* B))
    (f₀ : F) (w : List (F × A)) where
  Edge : Type
  fintype : Fintype Edge
  ribbon : Ribbon Edge
  balanced : @OpenBalanced Edge V F A B fintype _ _ ribbon Inc ι
  planar : @Ribbon.GenusZero Edge fintype ribbon
  anchor : Edge
  boundary : List Edge
  nodup : (anchor :: boundary).Nodup
  rotation : Follows ribbon.black (anchor :: boundary)
  exposed : ∀ x, balanced.blackLabel x = none ↔ x ∈ anchor :: boundary
  anchor_weight : balanced.weight anchor = 1
  anchor_label : balanced.whiteLabel anchor = f₀
  word : boundary.map (fun x => (balanced.whiteLabel x, balanced.weight x)) = w

attribute [instance] OpenDiagram.fintype

omit [Fintype α] [Fintype β] in
 def OpenDiagram.close (f₀ : F) (D : OpenDiagram Inc ι f₀ [])
    (v₀ : V) (hv : Inc v₀ f₀) : NoncommBalanced D.ribbon Inc ι := by
  have hb : D.boundary = [] := List.map_eq_nil_iff.mp D.word
  have hn (x : D.Edge) : D.balanced.blackLabel x = none ↔ x = D.anchor := by
    simpa only [hb, List.mem_cons, List.not_mem_nil, or_false] using D.exposed x
  let bl : D.Edge → V := fun x => (D.balanced.blackLabel x).getD v₀
  have heval (x : D.Edge) : ι (bl x) (D.balanced.whiteLabel x) (D.balanced.weight x) =
      augMap ι (D.balanced.blackLabel x) (D.balanced.whiteLabel x) (D.balanced.weight x) := by
    cases h : D.balanced.blackLabel x with
    | none =>
      have hx := (hn x).mp h
      rw [hx, D.anchor_weight]
      simp
    | some v => simp [bl, h, augMap]
  exact {
    blackLabel := bl
    whiteLabel := D.balanced.whiteLabel
    blackLabel_rot := fun x => congrArg (fun v => v.getD v₀) (D.balanced.blackLabel_rot x)
    whiteLabel_rot := D.balanced.whiteLabel_rot
    incident := fun x => by
      cases h : D.balanced.blackLabel x with
      | none =>
        have hx := (hn x).mp h
        have hanc := (hn D.anchor).mpr rfl
        simpa [bl, hx, hanc, D.anchor_label] using hv
      | some v =>
        have hi := D.balanced.incident x
        simpa [augInc, bl, h] using hi
    weight := D.balanced.weight
    white_prod := D.balanced.white_prod
    potential := D.balanced.potential
    exception := D.balanced.exception
    black_balance := fun x hx => by simpa only [heval] using D.balanced.black_balance x hx
    black_defect := by simpa only [heval] using D.balanced.black_defect }

omit [Fintype α] [Fintype β] in
 theorem OpenDiagram.not_empty (f₀ : F) (D : OpenDiagram Inc ι f₀ [])
    (v₀ : V) (hv : Inc v₀ f₀) (hshort : ShortWords Inc ι)
    (hgirth : 8 ≤ (incidenceGraph Inc).egirth) : False :=
  (D.close f₀ v₀ hv).not_genusZero hshort hgirth D.planar

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {α : Type portUniverse66} {V : Type portUniverse67} {F : Type portUniverse68} {A : Type portUniverse69} {B : Type portUniverse70} [Fintype α] [CommGroup A] [Group B]

lemma cycleSet_wheel_white (p : Perm α) (x : α ⊕ α) :
    cycleSet (Ribbon.wheel p).white (cycleClass _ x) =
      {Sum.inl (sumIndex x), Sum.inr (sumIndex x)} := by
  ext y
  rw [mem_cycleSet, cycleClass_eq]
  change (SameCycle.setoid (Ribbon.wheel p).white).r y x ↔ _
  rw [wheel_white_setoid]
  cases x <;> cases y <;> simp [sumIndex]

variable {Inc : V → F → Prop} {ι : V → F → (A →* B)}

def FlatOpenBalanced.wheel (p : Perm α) (v : V) (fl : α → F) (w : α → A)
    (hinc : ∀ x, Inc v (fl x)) (t : α → B)
    (ht : ∀ x, t (p x) = t x * ι v (fl x) (w x)) :
    FlatOpenBalanced (Ribbon.wheel p) Inc ι where
  blackLabel := Sum.elim (fun _ => none) (fun _ => some v)
  whiteLabel := Sum.elim fl fl
  blackLabel_rot := by rintro (x | x) <;> rfl
  whiteLabel_rot := by rintro (x | x) <;> rfl
  incident := by rintro (x | x); trivial; exact hinc x
  weight := Sum.elim w (fun x => (w x)⁻¹)
  white_prod c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change (∏ y ∈ cycleSet (Ribbon.wheel p).white (cycleClass _ x), Sum.elim w (fun x => (w x)⁻¹) y) = 1
      rw [cycleSet_wheel_white, Finset.prod_pair (by simp)]
      simp only [Sum.elim_inl, Sum.elim_inr, mul_inv_cancel]
  potential := Sum.elim (fun _ => 1) (fun x => t (p x))
  black_balance := by
    rintro (x | x)
    · simp [Ribbon.wheel, augMap]
    · change t (p (p⁻¹ x)) = t (p x) * ι v (fl x) ((w x)⁻¹)
      simp [ht x, mul_assoc]
  potential_none := by rintro (x | x) hx; rfl; exact (Option.some_ne_none v hx).elim

def OpenBalanced.wheel (p : Perm α) (v : V) (fl : α → F) (w : α → A)
    (hinc : ∀ x, Inc v (fl x)) (D : Holonomy.Defect p (fun x => ι v (fl x) (w x))) :
    OpenBalanced (Ribbon.wheel p) Inc ι where
  blackLabel := Sum.elim (fun _ => none) (fun _ => some v)
  whiteLabel := Sum.elim fl fl
  blackLabel_rot := by rintro (x | x) <;> rfl
  whiteLabel_rot := by rintro (x | x) <;> rfl
  incident := by rintro (x | x); trivial; exact hinc x
  weight := Sum.elim w (fun x => (w x)⁻¹)
  white_prod c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change (∏ y ∈ cycleSet (Ribbon.wheel p).white (cycleClass _ x), Sum.elim w (fun x => (w x)⁻¹) y) = 1
      rw [cycleSet_wheel_white, Finset.prod_pair (by simp)]
      simp only [Sum.elim_inl, Sum.elim_inr, mul_inv_cancel]
  potential := Sum.elim (fun _ => 1) (fun x => D.potential (p x))
  exception := .inr D.exception
  black_balance := by
    rintro (x | x) hx
    · simp [Ribbon.wheel, augMap]
    · have hx' : x ≠ D.exception := fun h => hx (congrArg Sum.inr h)
      change D.potential (p (p⁻¹ x)) = D.potential (p x) * ι v (fl x) ((w x)⁻¹)
      simp [D.balance x hx', mul_assoc]
  black_defect := by
    change D.potential (p (p⁻¹ D.exception)) ≠ D.potential (p D.exception) *
      ι v (fl D.exception) ((w D.exception)⁻¹)
    simp only [show p (p⁻¹ D.exception) = D.exception from p.apply_symm_apply _, map_inv]
    intro h
    apply D.defective
    have hh := congrArg (fun g => g * ι v (fl D.exception) (w D.exception)) h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm
  potential_none := by rintro (x | x) hx; rfl; exact (Option.some_ne_none v hx).elim
  exception_some := Option.some_ne_none v

omit [Fintype α] in
 def wordWheel (r : List (F × A)) (v : V)
    (hinc : ∀ t ∈ r, Inc v t.1)
    (hprod : (r.map (fun t => ι v t.1 t.2)).prod = 1) :
    FlatOpenBalanced (Ribbon.wheel (List.finRange r.length).formPerm) Inc ι :=
  FlatOpenBalanced.wheel _ v (fun i => (r.get i).1) (fun i => (r.get i).2)
    (fun i => hinc _ (List.get_mem r i))
    (listPotential (List.finRange r.length) (fun i => ι v (r.get i).1 (r.get i).2))
    (fun i => listPotential_balance _ (List.nodup_finRange _) _ (by
      change ((List.finRange r.length).map ((fun t : F × A => ι v t.1 t.2) ∘ r.get)).prod = 1
      rw [← List.map_map, List.map_get_finRange]
      exact hprod) i (by simp))

omit [Fintype α] in
 def OpenDiagram.initial (f₀ : F) (v : V) (hf₀ : Inc v f₀) (w : List (F × A))
    (hinc : ∀ t ∈ w, Inc v t.1)
    (hprod : (w.map (fun t => ι v t.1 t.2)).prod ≠ 1) :
    OpenDiagram Inc ι f₀ w := by
  classical
  let r := (f₀, (1 : A)) :: w
  let n := w.length + 1
  let p := (List.finRange n).formPerm
  let fl := fun i : Fin n => (r.get i).1
  let wt := fun i : Fin n => (r.get i).2
  have hr : ∀ i : Fin n, Inc v (fl i) := by
    intro i
    have hm := List.get_mem r i
    rcases List.mem_cons.mp hm with h | h
    · simpa only [fl, h] using hf₀
    · exact hinc _ h
  have hp : ((List.finRange n).map (fun i => ι v (fl i) (wt i))).prod ≠ 1 := by
    change ((List.finRange r.length).map (fun i => ι v (r.get i).1 (r.get i).2)).prod ≠ 1
    change ((List.finRange r.length).map ((fun t : F × A => ι v t.1 t.2) ∘ r.get)).prod ≠ 1
    rw [← List.map_map, List.map_get_finRange]
    simpa only [r, List.map_cons, List.prod_cons, map_one, one_mul] using hprod
  let E := listDefect (List.finRange n) (List.nodup_finRange n) (fun i => by simp)
    (fun i => ι v (fl i) (wt i)) hp
  let D := OpenBalanced.wheel (ι := ι) p v fl wt hr E
  let bd : List (Fin n ⊕ Fin n) := (List.finRange w.length).map (Sum.inl ∘ Fin.succ)
  have heq : Sum.inl (0 : Fin n) :: bd = (List.finRange n).map Sum.inl := by
    change Sum.inl (0 : Fin (w.length+1)) :: bd = (List.finRange (w.length+1)).map Sum.inl
    rw [List.finRange_succ, List.map_cons, List.map_map]
  refine {
    Edge := Fin n ⊕ Fin n
    fintype := inferInstance
    ribbon := Ribbon.wheel p
    balanced := D
    planar := Ribbon.genusZero_wheel p
    anchor := Sum.inl (0 : Fin n)
    boundary := bd
    nodup := ?_
    rotation := ?_
    exposed := ?_
    anchor_weight := rfl
    anchor_label := rfl
    word := ?_ }
  · rw [heq]
    exact (List.nodup_finRange n).map Sum.inl_injective
  · rw [heq]
    exact (follows_formPerm (List.finRange n)).map_sum_left
  · intro x
    rw [heq]
    cases x <;> simp [D, OpenBalanced.wheel]
  · change bd.map (fun x => (D.whiteLabel x, D.weight x)) = w
    dsimp only [bd]
    rw [List.map_map]
    change ((List.finRange w.length).map (fun i => w.get i)) = w
    exact List.map_get_finRange w

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {V : Type portUniverse71} {F : Type portUniverse72} {A : Type portUniverse73} {B : Type portUniverse74} [CommGroup A] [Group B]
variable {Inc : V → F → Prop} {ι : V → F → (A →* B)} {f₀ : F} {w : List (F × A)}

theorem OpenDiagram.deleteBlock (D : OpenDiagram Inc ι f₀ w)
    (pre r post : List D.Edge) (hboundary : D.boundary = pre ++ r ++ post)
    (v : V) (hinc : ∀ x ∈ r, Inc v (D.balanced.whiteLabel x))
    (hprod : (r.map fun x => ι v (D.balanced.whiteLabel x) (D.balanced.weight x)).prod = 1) :
    Nonempty (OpenDiagram Inc ι f₀ ((pre ++ post).map
      (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)))) := by
  classical
  cases r with
  | nil =>
    have hw : w = (pre ++ post).map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) := by
      exact D.word.symm.trans (congrArg _ (by simpa only [List.append_nil] using hboundary))
    exact ⟨hw ▸ D⟩
  | cons a r =>
    let M := post ++ D.anchor :: pre
    have hM : M ≠ [] := by simp [M]
    obtain ⟨b, m, hbm⟩ := List.exists_cons_of_ne_nil hM
    have hrot : Follows D.ribbon.black ((D.anchor :: pre) ++ ((a :: r) ++ post)) := by
      simpa only [hboundary, List.cons_append, List.append_assoc] using D.rotation
    have hnd : (((D.anchor :: pre) ++ ((a :: r) ++ post))).Nodup := by
      simpa only [hboundary, List.cons_append, List.append_assoc] using D.nodup
    have hrot' : Follows D.ribbon.black ((a :: r) ++ (b :: m)) := by
      simpa only [List.append_assoc, ← hbm] using hrot.append_rotate hnd
    have hnd' : ((a :: r) ++ (b :: m)).Nodup := by
      have hn := (List.nodup_append_comm).mp hnd
      simpa only [List.append_assoc, ← hbm] using hn
    have hmem (x : D.Edge) : x ∈ D.anchor :: D.boundary ↔ x ∈ (a :: r) ++ (b :: m) := by
      simp only [hboundary, ← hbm, M, List.mem_cons, List.mem_append]
      tauto
    have hab : D.ribbon.black.SameCycle a b := hrot'.sameCycle hnd'
      (by simp) (by simp)
    have habne : a ≠ b := by
      intro h
      exact (List.nodup_append.mp hnd').2.2 a (by simp) b (by simp) h
    have ha : D.balanced.blackLabel a = none :=
      (D.exposed a).mpr ((hmem a).mpr (by simp))
    have hb : D.balanced.blackLabel b = none :=
      (D.exposed b).mpr ((hmem b).mpr (by simp))
    let S := D.ribbon.swapBlack a b
    have hsplit := hrot'.split hnd'
    have hnone : ∀ x ∈ a :: r, D.balanced.blackLabel x = none := by
      intro x hx
      exact (D.exposed x).mpr ((hmem x).mpr (List.mem_append_left _ hx))
    let E := (D.balanced.joinNone a b ha hb).fill (a :: r)
      (List.nodup_append.mp hnd').1 hsplit.1 hnone v hinc hprod
    have hmrot : Follows S.black (D.anchor :: (pre ++ post)) := by
      have hh : Follows S.black (post ++ (D.anchor :: pre)) := by
        simpa only [← hbm, S, Ribbon.swapBlack, M] using hsplit.2
      have hn : (post ++ (D.anchor :: pre)).Nodup := by
        simpa only [← hbm] using (List.nodup_append.mp hnd').2.1
      simpa only [List.cons_append] using hh.append_rotate hn
    have hmnd : (D.anchor :: (pre ++ post)).Nodup := by
      have hn : (post ++ (D.anchor :: pre)).Nodup := by
        simpa only [← hbm] using (List.nodup_append.mp hnd').2.1
      simpa only [List.cons_append] using List.nodup_append_comm.mp hn
    have hrem (x : D.Edge) : x ∈ b :: m ↔ x ∈ D.anchor :: (pre ++ post) := by
      simp only [← hbm, M, List.mem_append, List.mem_cons]
      tauto
    exact ⟨{
      Edge := D.Edge
      fintype := inferInstance
      ribbon := S
      balanced := E
      planar := D.ribbon.genusZero_swapBlack_split D.planar a b habne hab
      anchor := D.anchor
      boundary := pre ++ post
      nodup := hmnd
      rotation := hmrot
      exposed := fun x => by
        change (if x ∈ a :: r then some v else D.balanced.blackLabel x) = none ↔ _
        by_cases hx : x ∈ a :: r
        · simp only [ite_eq_left hx, Option.some_ne_none, false_iff]
          exact fun h => (List.nodup_append.mp hnd').2.2 x hx x ((hrem x).mpr h) rfl
        · rw [ite_eq_right hx, D.exposed, hmem, List.mem_append]
          simpa only [hx, false_or] using hrem x
      anchor_weight := D.anchor_weight
      anchor_label := D.anchor_label
      word := rfl }⟩

end OddKaplansky.Planar

namespace OddKaplansky.Planar
open Equiv Equiv.Perm
variable {V F A B : Type} [CommGroup A] [Group B]
variable {Inc : V → F → Prop} {ι : V → F → (A →* B)}
variable {f₀ : F} {w : List (F × A)}

theorem OpenDiagram.insertBlock (D : OpenDiagram Inc ι f₀ w)
    (pre post : List D.Edge) (hboundary : D.boundary = pre ++ post)
    (r : List (F × A)) (v : V) (hinc : ∀ t ∈ r, Inc v t.1)
    (hprod : (r.map (fun t => ι v t.1 t.2)).prod = 1) :
    Nonempty (OpenDiagram Inc ι f₀
      (pre.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) ++ r ++
        post.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)))) := by
  classical
  by_cases hr : r = []
  · subst r
    have hw : w = pre.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) ++
        [] ++ post.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) := by
      exact D.word.symm.trans (by rw [hboundary, List.map_append, List.append_nil])
    exact ⟨hw ▸ D⟩
  let p := (List.finRange r.length).formPerm
  let W := wordWheel r v hinc hprod
  let T := D.ribbon.sum (Ribbon.wheel p)
  let E := D.balanced.sumZero W
  let f : D.Edge → D.Edge ⊕ (Fin r.length ⊕ Fin r.length) := Sum.inl
  let g : Fin r.length → D.Edge ⊕ (Fin r.length ⊕ Fin r.length) := Sum.inr ∘ Sum.inl
  let Q := (List.finRange r.length).map g
  let M := (post ++ D.anchor :: pre).map f
  have hqn : Q ≠ [] := by
    intro he
    have hh : r.length = 0 := by simpa only [Q, List.length_map, List.length_finRange, List.length_nil] using congrArg List.length he
    exact hr (List.length_eq_zero_iff.mp hh)
  have hmn : M ≠ [] := by simp [M]
  obtain ⟨a, l, hqa⟩ := List.exists_cons_of_ne_nil hqn
  obtain ⟨b, m, hmb⟩ := List.exists_cons_of_ne_nil hmn
  have hnd₀ : ((D.anchor :: pre) ++ post).Nodup := by
    simpa only [hboundary, List.cons_append] using D.nodup
  have hrot₀ : Follows D.ribbon.black ((D.anchor :: pre) ++ post) := by
    simpa only [hboundary, List.cons_append] using D.rotation
  have hndM : M.Nodup := (List.nodup_append_comm.mp hnd₀).map Sum.inl_injective
  have hndQ : Q.Nodup := (List.nodup_finRange _).map (Sum.inr_injective.comp Sum.inl_injective)
  have hM : Follows T.black M := by
    exact (hrot₀.append_rotate hnd₀).map_sum_left
  have hQ : Follows T.black Q := by
    have h : Follows (Ribbon.wheel p).black ((List.finRange r.length).map Sum.inl) :=
      (follows_formPerm (List.finRange r.length)).map_sum_left
    simpa only [List.map_map, T, Ribbon.sum, Q, g] using h.map_sum_right (p := D.ribbon.black)
  have hdis : List.Disjoint Q M := by
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hy
    exact Sum.inl_ne_inr (show (Sum.inl j : D.Edge ⊕ (Fin r.length ⊕ Fin r.length)) = Sum.inr (Sum.inl i) from hj)
  have hnd : (Q ++ M).Nodup := List.Nodup.append hndQ hndM hdis
  have hac : a ∈ Q := by rw [hqa]; simp
  have hbc : b ∈ M := by rw [hmb]; simp
  have hcomp : ¬ T.components.r a b := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hac
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hbc
    rw [Ribbon.sum_components]
    exact fun h => sumSetoid_cross _ _ j (Sum.inl i)
      ((sumSetoid D.ribbon.components (Ribbon.wheel p).components).iseqv.symm h)
  have hal : E.blackLabel a = none := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hac
    rfl
  have hbl : E.blackLabel b = none := by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hbc
    apply (D.exposed j).mpr
    simpa only [hboundary, List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using hj
  let S := T.swapBlack a b
  let Z := E.joinNone a b hal hbl
  have hrot : Follows S.black (Q ++ M) := by
    simp only [hqa, hmb] at hQ hM hdis ⊢
    exact hQ.merge hM hdis
  have hrot' : Follows S.black (f D.anchor :: (pre.map f ++ Q ++ post.map f)) := by
    have hh : Follows S.black ((Q ++ post.map f) ++ (f D.anchor :: pre.map f)) := by
      simpa only [M, List.map_append, List.map_cons, List.append_assoc] using hrot
    have hn : ((Q ++ post.map f) ++ (f D.anchor :: pre.map f)).Nodup := by
      simpa only [M, List.map_append, List.map_cons, List.append_assoc] using hnd
    simpa only [List.cons_append, List.append_assoc] using hh.append_rotate hn
  have hnd' : (f D.anchor :: (pre.map f ++ Q ++ post.map f)).Nodup := by
    have hn : ((Q ++ post.map f) ++ (f D.anchor :: pre.map f)).Nodup := by
      simpa only [M, List.map_append, List.map_cons, List.append_assoc] using hnd
    simpa only [List.cons_append, List.append_assoc] using List.nodup_append_comm.mp hn
  refine ⟨{
    Edge := D.Edge ⊕ (Fin r.length ⊕ Fin r.length)
    fintype := inferInstance
    ribbon := S
    balanced := Z
    planar := T.genusZero_swapBlack_merge (D.ribbon.genusZero_sum (Ribbon.wheel p) D.planar
      (Ribbon.genusZero_wheel p)) a b hcomp
    anchor := f D.anchor
    boundary := pre.map f ++ Q ++ post.map f
    nodup := hnd'
    rotation := hrot'
    exposed := ?_
    anchor_weight := D.anchor_weight
    anchor_label := D.anchor_label
    word := ?_ }⟩
  · rintro (x | (i | i))
    · change D.balanced.blackLabel x = none ↔ _
      rw [D.exposed, hboundary]
      simp [f, Q, g, List.mem_map, Function.comp_def, List.mem_append, List.mem_cons]
    · change (none : Option V) = none ↔ _
      simp [f, Q, g, List.mem_map, Function.comp_def]
    · change (some v : Option V) = none ↔ _
      simp [f, Q, g, List.mem_map, Function.comp_def]
  · change (pre.map f ++ Q ++ post.map f).map
        (fun x => (E.whiteLabel x, E.weight x)) = _
    simp only [List.map_append, List.map_map]
    congr 2
    dsimp only [Q]
    rw [List.map_map]
    change ((List.finRange r.length).map (fun i => r.get i)) = r
    exact List.map_get_finRange r

end OddKaplansky.Planar

namespace OddKaplansky.Planar
variable {V F A B : Type} [CommGroup A] [Group B]
variable {Inc : V → F → Prop} {ι : V → F → (A →* B)} {f₀ : F}

theorem OpenDiagram.deleteWordBlock (pre r post : List (F × A))
    (v : V) (hinc : ∀ t ∈ r, Inc v t.1)
    (hprod : (r.map (fun t => ι v t.1 t.2)).prod = 1)
    (D : OpenDiagram Inc ι f₀ (pre ++ r ++ post)) :
    Nonempty (OpenDiagram Inc ι f₀ (pre ++ post)) := by
  classical
  obtain ⟨p, q, hpq, hp, hq⟩ := List.map_eq_append_iff.mp
    (D.word.trans (List.append_assoc pre r post))
  obtain ⟨s, t, hst, hs, ht⟩ := List.map_eq_append_iff.mp hq
  have hboundary : D.boundary = p ++ s ++ t := by
    exact hpq.trans ((congrArg (p ++ ·) hst).trans (List.append_assoc p s t).symm)
  have hnd : s.Nodup := by
    have hh := D.nodup.tail
    rw [hboundary] at hh
    exact (List.nodup_append.mp (List.nodup_append.mp hh).1).2.1
  have hinc' : ∀ x ∈ s, Inc v (D.balanced.whiteLabel x) := by
    intro x hx
    apply hinc (D.balanced.whiteLabel x, D.balanced.weight x)
    simpa only [hs] using (List.mem_map_of_mem (f := fun x =>
      (D.balanced.whiteLabel x, D.balanced.weight x)) hx)
  have hprod' : (s.map fun x =>
      ι v (D.balanced.whiteLabel x) (D.balanced.weight x)).prod = 1 := by
    have hh := hprod
    rw [← hs, List.map_map] at hh
    exact hh
  obtain ⟨E⟩ := D.deleteBlock p s t hboundary v hinc' hprod'
  have he : (p ++ t).map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) =
      pre ++ post := by rw [List.map_append, hp, ht]
  exact ⟨he ▸ E⟩

theorem OpenDiagram.insertWordBlock (pre r post : List (F × A))
    (v : V) (hinc : ∀ t ∈ r, Inc v t.1)
    (hprod : (r.map (fun t => ι v t.1 t.2)).prod = 1)
    (D : OpenDiagram Inc ι f₀ (pre ++ post)) :
    Nonempty (OpenDiagram Inc ι f₀ (pre ++ r ++ post)) := by
  obtain ⟨p, q, hpq, hp, hq⟩ := List.map_eq_append_iff.mp D.word
  obtain ⟨E⟩ := D.insertBlock p q hpq r v hinc hprod
  rw [hp, hq] at E
  exact ⟨E⟩

end OddKaplansky.Planar

namespace OddKaplansky.WordReduction
variable {α : Type portUniverse75}
abbrev Word (α : Type portUniverse76) := List (α × Bool)

inductive Delete (Allowed : Word α → Prop) : Word α → Word α → Prop
  | block (pre r post : Word α) (hr : Allowed r) :
      Delete Allowed (pre ++ r ++ post) (pre ++ post)

abbrev Related (Allowed : Word α → Prop) := Relation.EqvGen (Delete Allowed)

variable {Allowed : Word α → Prop}

lemma rel_trans {u v w : Word α} (h₁ : Related Allowed u v) (h₂ : Related Allowed v w) :
    Related Allowed u w := Relation.EqvGen.trans _ _ _ h₁ h₂

lemma rel_symm {u v : Word α} (h : Related Allowed u v) :
    Related Allowed v u := Relation.EqvGen.symm _ _ h

lemma Related.append_left {u v : Word α} (h : Related Allowed u v) (w : Word α) :
    Related Allowed (w ++ u) (w ++ v) := by
  induction h with
  | rel x y h =>
    cases h with
    | block pre r post hr =>
      simpa only [List.append_assoc] using Relation.EqvGen.rel _ _ (Delete.block (w ++ pre) r post hr)
  | refl x => exact .refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

lemma Related.append_right {u v : Word α} (h : Related Allowed u v) (w : Word α) :
    Related Allowed (u ++ w) (v ++ w) := by
  induction h with
  | rel x y h =>
    cases h with
    | block pre r post hr =>
      simpa only [List.append_assoc] using Relation.EqvGen.rel _ _ (Delete.block pre r (post ++ w) hr)
  | refl x => exact .refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

lemma Related.inv (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w))
    {u v : Word α} (h : Related Allowed u v) :
    Related Allowed (FreeGroup.invRev u) (FreeGroup.invRev v) := by
  induction h with
  | rel x y h =>
    cases h with
    | block pre r post hr =>
      simpa only [FreeGroup.invRev_append, List.append_assoc] using
        Relation.EqvGen.rel _ _ (Delete.block (FreeGroup.invRev post) (FreeGroup.invRev r)
          (FreeGroup.invRev pre) (hinv r hr))
  | refl x => exact .refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

lemma related_of_red_step
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    {u v : Word α} (h : FreeGroup.Red.Step u v) : Related Allowed u v := by
  cases h with
  | @not pre post a b =>
    simpa using Relation.EqvGen.rel _ _ (Delete.block pre [(a, b), (a, !b)] post (hcancel a b))

lemma related_of_red
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    {u v : Word α} (h : FreeGroup.Red u v) : Related Allowed u v := by
  induction h with
  | refl => exact .refl _
  | tail h hstep ih => exact rel_trans ih (related_of_red_step hcancel hstep)

lemma related_of_mk_eq
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    {u v : Word α} (h : FreeGroup.mk u = FreeGroup.mk v) : Related Allowed u v := by
  obtain ⟨w, huw, hvw⟩ := FreeGroup.Red.exact.mp h
  exact rel_trans (related_of_red hcancel huw) (rel_symm (related_of_red hcancel hvw))

lemma related_append_null {u v : Word α} (hu : Related Allowed u [])
    (hv : Related Allowed v []) : Related Allowed (u ++ v) [] := by
  exact rel_trans (hu.append_right v) (by simpa using hv)

def nullSubgroup (Allowed : Word α → Prop)
    (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w)) : Subgroup (FreeGroup α) where
  carrier g := ∃ w : Word α, FreeGroup.mk w = g ∧ Related Allowed w []
  one_mem' := ⟨[], rfl, .refl _⟩
  mul_mem' := by
    rintro _ _ ⟨u, rfl, hu⟩ ⟨v, rfl, hv⟩
    exact ⟨u ++ v, FreeGroup.mul_mk.symm, related_append_null hu hv⟩
  inv_mem' := by
    rintro _ ⟨w, rfl, hw⟩
    exact ⟨FreeGroup.invRev w, FreeGroup.inv_mk.symm, by simpa using hw.inv hinv⟩

lemma nullSubgroup_normal
    (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w))
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)]) :
    (nullSubgroup Allowed hinv).Normal := by
  constructor
  rintro g ⟨w, rfl, hw⟩ u
  induction u using Quot.inductionOn with
  | h v =>
    change ∃ z, FreeGroup.mk z = FreeGroup.mk v * FreeGroup.mk w * (FreeGroup.mk v)⁻¹ ∧ _
    refine ⟨v ++ w ++ FreeGroup.invRev v, ?_, ?_⟩
    · rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
    · have h₁ := (hw.append_left v).append_right (FreeGroup.invRev v)
      simp only [List.append_nil] at h₁
      apply rel_trans h₁
      apply related_of_mk_eq hcancel
      rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
      simp only [mul_inv_cancel, ← FreeGroup.one_eq_mk]

theorem of_presented_eq_one (rels : Set (FreeGroup α))
    (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w))
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    (hrels : ∀ g ∈ rels, ∃ w : Word α, FreeGroup.mk w = g ∧ Allowed w)
    (w : Word α) (hw : PresentedGroup.mk rels (FreeGroup.mk w) = 1) :
    Related Allowed w [] := by
  let H := nullSubgroup Allowed hinv
  let : H.Normal := nullSubgroup_normal hinv hcancel
  have hle : Subgroup.normalClosure rels ≤ H := by
    apply Subgroup.normalClosure_le_normal
    intro g hg
    obtain ⟨v, hv, hA⟩ := hrels g hg
    refine ⟨v, hv, ?_⟩
    simpa using Relation.EqvGen.rel _ _ (Delete.block [] v [] hA)
  obtain ⟨v, hv, hnull⟩ := hle (PresentedGroup.mk_eq_one_iff.mp hw)
  exact rel_trans (related_of_mk_eq hcancel hv.symm) hnull

end OddKaplansky.WordReduction

namespace OddKaplansky.Planar
variable {V F A B X : Type} [CommGroup A] [Group B]
variable {Inc : V → F → Prop} {ι : V → F → (A →* B)} {f₀ : F}

theorem OpenDiagram.related_iff (token : X × Bool → F × A)
    (Allowed : List (X × Bool) → Prop)
    (hA : ∀ r, Allowed r → ∃ v, (∀ t ∈ r.map token, Inc v t.1) ∧
      ((r.map token).map (fun t => ι v t.1 t.2)).prod = 1)
    {u w : List (X × Bool)} (h : WordReduction.Related Allowed u w) :
    Nonempty (OpenDiagram Inc ι f₀ (u.map token)) ↔
      Nonempty (OpenDiagram Inc ι f₀ (w.map token)) := by
  induction h with
  | rel u w h =>
    cases h with
    | block pre r post hr =>
      obtain ⟨v, hi, hs⟩ := hA r hr
      simp only [List.map_append]
      constructor
      · rintro ⟨D⟩
        exact D.deleteWordBlock _ _ _ v hi hs
      · rintro ⟨D⟩
        exact D.insertWordBlock _ _ _ v hi hs
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end OddKaplansky.Planar

namespace OddKaplansky.GluedGroup
noncomputable section
open scoped Classical
variable {V F A B : Type} [CommGroup A] [Group B]
variable (Inc : V → F → Prop) (ι : V → F → (A →* B))

abbrev Generator := F × A
abbrev LocalGenerator (v : V) := {s : Generator (F := F) (A := A) // Inc v s.1}

def includeLocal (v : V) : FreeGroup (LocalGenerator (A := A) Inc v) →*
    FreeGroup (Generator (F := F) (A := A)) := FreeGroup.map Subtype.val

def localEvaluation (v : V) : FreeGroup (LocalGenerator (A := A) Inc v) →* B :=
  FreeGroup.lift (fun s => ι v s.val.1 s.val.2)

def relators : Set (FreeGroup (Generator (F := F) (A := A))) :=
  {g | ∃ (v : V) (w : FreeGroup (LocalGenerator (A := A) Inc v)),
    localEvaluation Inc ι v w = 1 ∧ includeLocal Inc v w = g}

abbrev N := PresentedGroup (relators Inc ι)

def fromLocal (v : V) : FreeGroup (LocalGenerator (A := A) Inc v) →* N Inc ι :=
  (PresentedGroup.mk (relators Inc ι)).comp (includeLocal Inc v)

lemma local_kernel_le (v : V) : (localEvaluation Inc ι v).ker ≤ (fromLocal Inc ι v).ker := by
  intro w hw
  exact PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure ⟨v, w, hw, rfl⟩)

def signedToken (s : Generator (F := F) (A := A) × Bool) : F × A :=
  (s.1.1, if s.2 then s.1.2 else s.1.2⁻¹)

def Allowed (w : List (Generator (F := F) (A := A) × Bool)) : Prop :=
  ∃ v : V, (∀ t ∈ w.map signedToken, Inc v t.1) ∧
    ((w.map signedToken).map (fun t => ι v t.1 t.2)).prod = 1

lemma signedToken_inv (s : Generator (F := F) (A := A) × Bool) :
    signedToken (s.1, !s.2) = ((signedToken s).1, (signedToken s).2⁻¹) := by
  rcases s with ⟨s, b⟩
  cases b <;> simp [signedToken]

lemma allowed_inv (w : List (Generator (F := F) (A := A) × Bool))
    (h : Allowed Inc ι w) : Allowed Inc ι (FreeGroup.invRev w) := by
  obtain ⟨v, hi, hp⟩ := h
  refine ⟨v, ?_, ?_⟩
  · intro t ht
    simp only [FreeGroup.invRev, List.map_reverse, List.map_map, List.mem_reverse,
      List.mem_map] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    change Inc v (signedToken (s.1, !s.2)).1
    rw [signedToken_inv]
    exact hi (signedToken s) (List.mem_map_of_mem hs)
  · simp only [FreeGroup.invRev, List.map_reverse, List.map_map, Function.comp_def,
      signedToken_inv, map_inv]
    have hinv : ((w.map (fun s => (ι v (signedToken s).1 (signedToken s).2)⁻¹)).reverse).prod =
        ((w.map (fun s => ι v (signedToken s).1 (signedToken s).2)).prod)⁻¹ := by
      clear hi hp
      induction w with
      | nil => simp
      | cons a w ih => simp [ih, mul_inv_rev]
    rw [hinv]
    simpa only [List.map_map, Function.comp_def, inv_eq_one] using hp

lemma allowed_cancel (hInc : ∀ f, ∃ v, Inc v f)
    (g : Generator (F := F) (A := A)) (b : Bool) :
    Allowed Inc ι [(g, b), (g, !b)] := by
  obtain ⟨v, hv⟩ := hInc g.1
  refine ⟨v, ?_, ?_⟩
  · intro t ht
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact hv
  · cases b <;> simp [signedToken]

lemma localEvaluation_word (v : V) (w : List (LocalGenerator (A := A) Inc v × Bool)) :
    localEvaluation Inc ι v (FreeGroup.mk w) =
      ((w.map (fun s => (s.1.val, s.2))).map (fun s =>
        ι v (signedToken s).1 (signedToken s).2)).prod := by
  rw [localEvaluation, FreeGroup.lift_mk, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  rcases s with ⟨s, b⟩
  cases b <;> simp [signedToken]

lemma relators_allowed (g : FreeGroup (Generator (F := F) (A := A)))
    (hg : g ∈ relators Inc ι) :
    ∃ w, FreeGroup.mk w = g ∧ Allowed Inc ι w := by
  obtain ⟨v, r, he, rfl⟩ := hg
  induction r using Quot.inductionOn with
  | h w =>
    refine ⟨w.map (fun s => (s.1.val, s.2)), rfl, v, ?_, ?_⟩
    · intro t ht
      simp only [List.map_map, List.mem_map] at ht
      obtain ⟨s, _, rfl⟩ := ht
      exact s.1.property
    · change localEvaluation Inc ι v (FreeGroup.mk w) = 1 at he
      simpa only [localEvaluation_word, List.map_map, Function.comp_def] using he

theorem fromLocal_eq_one_iff (hInc : ∀ f, ∃ v, Inc v f)
    (hshort : Planar.ShortWords Inc ι)
    (hgirth : 8 ≤ (Planar.incidenceGraph Inc).egirth)
    (v : V) (w : FreeGroup (LocalGenerator (A := A) Inc v)) :
    fromLocal Inc ι v w = 1 ↔ localEvaluation Inc ι v w = 1 := by
  refine ⟨?_, fun h => local_kernel_le Inc ι v h⟩
  intro hw
  by_contra he
  induction w using Quot.inductionOn with
  | h w =>
    have hp : ((w.map (fun s => (s.1.val, s.2))).map
        (fun s => ι v (signedToken s).1 (signedToken s).2)).prod ≠ 1 := by
      change localEvaluation Inc ι v (FreeGroup.mk w) ≠ 1 at he
      simpa only [localEvaluation_word] using he
    have hne : w ≠ [] := by rintro rfl; simp at hp
    obtain ⟨s, z, rfl⟩ := List.exists_cons_of_ne_nil hne
    let q := (s :: z).map (fun s => (s.1.val, s.2))
    have hq : WordReduction.Related (Allowed Inc ι) q [] :=
      WordReduction.of_presented_eq_one (relators Inc ι)
        (allowed_inv Inc ι) (allowed_cancel Inc ι hInc)
        (relators_allowed Inc ι) q hw
    have hi : Nonempty (Planar.OpenDiagram Inc ι s.1.val.1 (q.map signedToken)) := by
      refine ⟨Planar.OpenDiagram.initial _ v s.1.property _ ?_ ?_⟩
      · intro t ht
        simp only [q, List.map_map, List.mem_map] at ht
        obtain ⟨a, _, rfl⟩ := ht
        exact a.1.property
      · simpa only [q, List.map_map, Function.comp_def] using hp
    obtain ⟨D⟩ := (Planar.OpenDiagram.related_iff (Inc := Inc) (ι := ι)
      (f₀ := s.1.val.1) signedToken (Allowed Inc ι) (fun _ h => h) hq).mp hi
    exact D.not_empty _ v s.1.property hshort hgirth

abbrev Local (v : V) := (localEvaluation Inc ι v).range

def theta (v : V) : Local Inc ι v →* N Inc ι :=
  (localEvaluation Inc ι v).rangeRestrict.liftOfSurjective
    (localEvaluation Inc ι v).rangeRestrict_surjective
    ⟨fromLocal Inc ι v, by
      intro w hw
      apply local_kernel_le Inc ι v
      exact congrArg Subtype.val hw⟩

lemma theta_evaluation (v : V) (w : FreeGroup (LocalGenerator (A := A) Inc v)) :
    theta Inc ι v ((localEvaluation Inc ι v).rangeRestrict w) = fromLocal Inc ι v w := by
  simp [theta]

theorem theta_injective (hInc : ∀ f, ∃ v, Inc v f)
    (hshort : Planar.ShortWords Inc ι) (hgirth : 8 ≤ (Planar.incidenceGraph Inc).egirth)
    (v : V) : Function.Injective (theta Inc ι v) := by
  apply (theta Inc ι v).ker_eq_bot_iff.mp
  apply bot_unique
  intro a ha
  change a = 1
  obtain ⟨w, rfl⟩ := (localEvaluation Inc ι v).rangeRestrict_surjective a
  apply Subtype.ext
  apply (fromLocal_eq_one_iff Inc ι hInc hshort hgirth v w).mp
  simpa only [MonoidHom.mem_ker, theta_evaluation] using ha

end
end OddKaplansky.GluedGroup

namespace OddKaplansky.GluedGroup
open scoped Classical
variable {V F A B : Type} [CommGroup A] [Group B]
variable (Inc : V → F → Prop) (ι : V → F → (A →* B))

noncomputable def localEdge (v : V) (f : F) (hf : Inc v f) (a : A) : Local Inc ι v :=
  (localEvaluation Inc ι v).rangeRestrict (FreeGroup.of ⟨(f, a), hf⟩)

@[simp] lemma localEdge_val (v : V) (f : F) (hf : Inc v f) (a : A) :
    (localEdge Inc ι v f hf a : B) = ι v f a := by
  change localEvaluation Inc ι v (FreeGroup.of ⟨(f, a), hf⟩) = ι v f a
  simp [localEvaluation]

@[simp] lemma theta_localEdge (v : V) (f : F) (hf : Inc v f) (a : A) :
    theta Inc ι v (localEdge Inc ι v f hf a) = PresentedGroup.of (f, a) := by
  rw [localEdge, theta_evaluation]
  simp [fromLocal, includeLocal, PresentedGroup.of]
end OddKaplansky.GluedGroup

end
end
end

end OAI
