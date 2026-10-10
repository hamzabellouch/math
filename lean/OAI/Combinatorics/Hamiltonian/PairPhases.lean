import OAI.Combinatorics.Hamiltonian.CycleReversal

namespace OAI

/-! Paired states, permutation cycle classes, and phase cancellation. -/

namespace Barnette

noncomputable def phase (n : ℤ) : ℂ := Complex.I ^ (n / 3)

theorem phase_add_six (n : ℤ) : phase (n + 6) = -phase n := by
  unfold phase
  have h : (n + 6) / 3 = n / 3 + 2 := by omega
  rw [h, zpow_add₀ Complex.I_ne_zero]
  norm_num

theorem phase_sub_six (n : ℤ) : phase (n - 6) = -phase n := by
  have h := phase_add_six (n - 6)
  rw [sub_add_cancel] at h
  exact neg_eq_iff_eq_neg.mp h.symm

theorem disk_count_identity {B W I h l : ℤ}
    (heuler : B + W = 2 * I + h - 2) (hsides : 3 * (B - W) = 2 * l - h)
    (hmatching : B = I + l) : 2 * l - h = -3 := by omega

namespace TriangleSystem

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

def rawIndexSum [Fintype A] (r s : T.State X) : ℤ :=
  ∑ t, indexDelta (r.val t) (s.val t)

noncomputable instance [Fintype A] (s : T.State X) : Fintype (T.Partners s) :=
  Fintype.ofFinite {r : T.State X // T.Partner r s}

namespace OppositeCycle

variable {s : T.State X} (C : T.OppositeCycle s)

noncomputable def faceSet : Finset A := by
  classical
  exact Finset.univ.image C.face

@[simp] theorem mem_faceSet (t : A) : t ∈ C.faceSet ↔ t ∈ Set.range C.face := by
  classical
  simp [faceSet]

def cyclicDelta (r : T.State X) : ℤ :=
  ∑ i, indexDelta (r.val (C.face i)) (thirdIndex (r.val (C.face i)) (s.val (C.face i)))

theorem reverse_rawIndexSum_diff [Fintype A] (r : T.State X) (hrs : T.Partner r s) :
    rawIndexSum (C.reverse r hrs) s - rawIndexSum r s = 2 * C.cyclicDelta r := by
  classical
  rw [rawIndexSum, rawIndexSum, ← Finset.sum_sub_distrib]
  let h (t : A) := indexDelta ((C.reverse r hrs).val t) (s.val t) -
    indexDelta (r.val t) (s.val t)
  change ∑ t, h t = _
  calc
    ∑ t, h t = ∑ t ∈ C.faceSet, h t := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro t _ ht
      have hnot : t ∉ Set.range C.face := fun h => ht ((C.mem_faceSet t).mpr h)
      simp only [h, reverse_val, changedCorners, ite_eq_right hnot, sub_self]
    _ = ∑ t ∈ C.faceSet,
        2 * indexDelta (r.val t) (thirdIndex (r.val t) (s.val t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hrst : r.val t ≠ s.val t := fun h => hrs t ((State.value_eq_iff r s t).mpr h)
      change indexDelta (C.changedCorners r t) (s.val t) -
        indexDelta (r.val t) (s.val t) = _
      rw [changedCorners, ite_eq_left ((C.mem_faceSet t).mp ht)]
      exact indexDelta_third _ _ hrst
    _ = ∑ i, 2 * indexDelta (r.val (C.face i))
        (thirdIndex (r.val (C.face i)) (s.val (C.face i))) := by
      unfold faceSet
      apply Finset.sum_image
      exact C.face.injective.injOn
    _ = 2 * C.cyclicDelta r := by rw [cyclicDelta, Finset.mul_sum]

theorem reverse_phase [Fintype A] (r : T.State X) (hrs : T.Partner r s)
    (hdisk : C.cyclicDelta r = 3 ∨ C.cyclicDelta r = -3) :
    phase (rawIndexSum (C.reverse r hrs) s) = -phase (rawIndexSum r s) := by
  have hdiff := C.reverse_rawIndexSum_diff r hrs
  rcases hdisk with h | h
  · have heq : rawIndexSum (C.reverse r hrs) s = rawIndexSum r s + 6 := by omega
    rw [heq, phase_add_six]
  · have heq : rawIndexSum (C.reverse r hrs) s = rawIndexSum r s - 6 := by omega
    rw [heq, phase_sub_six]

theorem fixed_second_state_cancels [Fintype A] {M : Type*} [AddCommGroup M] [Module ℂ M]
    (hdisk : ∀ r : T.Partners s, C.cyclicDelta r.val = 3 ∨ C.cyclicDelta r.val = -3)
    (weight : M) : (∑ r : T.Partners s, phase (rawIndexSum r.val s) • weight) = 0 := by
  classical
  apply Finset.sum_ninvolution C.reversal
  · intro r
    change phase (rawIndexSum r.val s) • weight +
      phase (rawIndexSum (C.reverse r.val r.property) s) • weight = 0
    rw [C.reverse_phase r.val r.property (hdisk r), neg_smul, add_neg_cancel]
  · intro r _
    exact C.reversal_ne r
  · intro r
    exact Finset.mem_univ _
  · intro r
    exact C.reversal_involutive r

end OppositeCycle
end TriangleSystem
end Barnette

namespace Barnette

variable {A : Type*}

def CycleClass (p : Equiv.Perm A) := Quotient (Equiv.Perm.SameCycle.setoid p)

def classOf (p : Equiv.Perm A) (a : A) : CycleClass p := Quotient.mk _ a

noncomputable instance [Finite A] (p : Equiv.Perm A) : Fintype (CycleClass p) :=
  Fintype.ofFinite (Quotient (Equiv.Perm.SameCycle.setoid p))

@[simp] theorem classOf_apply (p : Equiv.Perm A) (a : A) : classOf p (p a) = classOf p a := by
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl p a).apply_left

@[simp] theorem classOf_symm_apply (p : Equiv.Perm A) (a : A) :
    classOf p (p.symm a) = classOf p a := by
  have h := classOf_apply p (p.symm a)
  simpa using h.symm

theorem classOf_surjective (p : Equiv.Perm A) : Function.Surjective (classOf p) :=
  Quotient.mk_surjective

theorem classOf_eq_iff (p : Equiv.Perm A) (a b : A) :
    classOf p a = classOf p b ↔ p.SameCycle a b := Quotient.eq

theorem invariant_on_cycle [Finite A] {p : Equiv.Perm A} {B : Type*} (f : A → B)
    (hf : ∀ a, f (p a) = f a) {a b : A} (hab : p.SameCycle a b) : f a = f b := by
  obtain ⟨n, rfl⟩ := hab.exists_nat_pow_eq
  have hpow : ∀ n : ℕ, ∀ a, f ((p ^ n) a) = f a := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [pow_succ', Equiv.Perm.mul_apply, hf, ih]
  exact (hpow n a).symm

noncomputable def descendCycle [Finite A] {p : Equiv.Perm A} {B : Type*} (f : A → B)
    (hf : ∀ a, f (p a) = f a) : CycleClass p → B :=
  Quotient.lift f (fun _ _ h => invariant_on_cycle f hf h)

@[simp] theorem descendCycle_classOf [Finite A] {p : Equiv.Perm A} {B : Type*} (f : A → B)
    (hf : ∀ a, f (p a) = f a) (a : A) : descendCycle f hf (classOf p a) = f a := rfl

def partialPerm (p : Equiv.Perm A) (b : A → Bool) (hb : ∀ a, b (p a) = b a) : Equiv.Perm A where
  toFun a := if b a then p a else a
  invFun a := if b a then p.symm a else a
  left_inv a := by
    cases h : b a <;> simp [h, hb]
  right_inv a := by
    have hb' (a) : b (p.symm a) = b a := by simpa using (hb (p.symm a)).symm
    cases h : b a <;> simp [h, hb']

@[simp] theorem partialPerm_apply (p : Equiv.Perm A) (b : A → Bool)
    (hb : ∀ a, b (p a) = b a) (a : A) :
    partialPerm p b hb a = if b a then p a else a := rfl

end Barnette

namespace Barnette.TriangleSystem

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

def State.ofPermutation (s : T.State X) (e : Equiv.Perm A) (c : A → Fin 3)
    (hc : ∀ t, T.vertex t (c t) = s.value (e t)) : T.State X :=
  ⟨c, by
    constructor
    · intro t u h
      exact e.injective (s.value_injective (by simpa only [hc] using h))
    · rw [← s.value_range]
      ext v
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨e t, (hc t).symm⟩
      · rintro ⟨t, rfl⟩
        exact ⟨e.symm t, (hc _).trans (congrArg s.value (e.apply_symm_apply t))⟩⟩

def Pair (X : Set V) := {rs : T.State X × T.State X // T.Partner rs.1 rs.2}

namespace Pair

def left (P : @Pair A V T X) : T.State X := P.val.1
def right (P : @Pair A V T X) : T.State X := P.val.2

theorem partner (P : @Pair A V T X) : T.Partner P.left P.right := P.property

@[ext] theorem ext {P Q : @Pair A V T X} (hl : P.left = Q.left)
    (hr : P.right = Q.right) : P = Q := Subtype.ext (Prod.ext hl hr)

instance [Finite A] : Finite (@Pair A V T X) := inferInstanceAs (Finite (Subtype _))
noncomputable instance [Fintype A] : Fintype (@Pair A V T X) := Fintype.ofFinite _

noncomputable def next (P : @Pair A V T X) : Equiv.Perm A :=
  P.right.toEquiv.trans P.left.toEquiv.symm

@[simp] theorem value_next (P : @Pair A V T X) (t : A) :
    P.left.value (P.next t) = P.right.value t := by
  change (P.left.toEquiv (P.left.toEquiv.symm (P.right.toEquiv t)) : V) = _
  rw [Equiv.apply_symm_apply, State.coe_toEquiv]

@[simp] theorem value_prev (P : @Pair A V T X) (t : A) :
    P.right.value (P.next.symm t) = P.left.value t := by
  have h := P.value_next (P.next.symm t)
  simpa using h.symm

theorem next_ne (P : @Pair A V T X) (t : A) : P.next t ≠ t := by
  intro h
  exact P.partner t (by simpa only [h] using P.value_next t)

def third (P : @Pair A V T X) : A → Fin 3 :=
  fun t => thirdIndex (P.left.val t) (P.right.val t)

def Group (P : @Pair A V T X) := {Q : @Pair A V T X // Q.third = P.third}

noncomputable instance [Fintype A] (P : @Pair A V T X) : Fintype P.Group :=
  Fintype.ofFinite {Q : @Pair A V T X // Q.third = P.third}

def flipCorners (r s : T.State X) (b : A → Bool) : A → Fin 3 :=
  fun t => if b t then s.val t else r.val t

noncomputable def flipLeft (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) : T.State X :=
  P.left.ofPermutation (partialPerm P.next b hb) (flipCorners P.left P.right b) (by
    intro t
    cases h : b t
    · simp [flipCorners, h, State.value]
    · simpa only [flipCorners, h, ↓reduceIte, partialPerm_apply, State.value] using
        (P.value_next t).symm)

noncomputable def flipRight (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) : T.State X :=
  P.right.ofPermutation
    (partialPerm P.next.symm b (fun t => by simpa using (hb (P.next.symm t)).symm))
    (flipCorners P.right P.left b) (by
      intro t
      cases h : b t
      · simp [flipCorners, h, State.value]
      · simpa only [flipCorners, h, ↓reduceIte, partialPerm_apply, State.value] using
          (P.value_prev t).symm)

@[simp] theorem flipLeft_val (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) :
    (P.flipLeft b hb).val = flipCorners P.left P.right b := rfl

@[simp] theorem flipRight_val (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) :
    (P.flipRight b hb).val = flipCorners P.right P.left b := rfl

@[simp] theorem flipLeft_value (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) (t : A) :
    (P.flipLeft b hb).value t = if b t then P.right.value t else P.left.value t := by
  cases h : b t <;> simp [State.value, flipLeft_val, flipCorners, h]

@[simp] theorem flipRight_value (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) (t : A) :
    (P.flipRight b hb).value t = if b t then P.left.value t else P.right.value t := by
  cases h : b t <;> simp [State.value, flipRight_val, flipCorners, h]

noncomputable def flip (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) : @Pair A V T X :=
  ⟨(P.flipLeft b hb, P.flipRight b hb), by
    intro t
    change (P.flipLeft b hb).value t ≠ (P.flipRight b hb).value t
    rw [flipLeft_value, flipRight_value]
    cases h : b t
    · simpa [h] using P.partner t
    · simpa [h] using (P.partner t).symm⟩

theorem flip_third (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) : (P.flip b hb).third = P.third := by
  funext t
  change thirdIndex (flipCorners P.left P.right b t) (flipCorners P.right P.left b t) = _
  cases h : b t <;> simp [flipCorners, h, third, thirdIndex, add_comm]

noncomputable def orient (P : @Pair A V T X) (b : CycleClass P.next → Bool) : P.Group :=
  ⟨P.flip (fun t => b (classOf P.next t)) (fun t => by rw [classOf_apply]),
    P.flip_third _ _⟩

theorem same_third_corners : ∀ i j k l : Fin 3, i ≠ j → k ≠ l →
    thirdIndex i j = thirdIndex k l → (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by decide

theorem group_local (P : @Pair A V T X) (Q : P.Group) (t : A) :
    (Q.val.left.val t = P.left.val t ∧ Q.val.right.val t = P.right.val t) ∨
    (Q.val.left.val t = P.right.val t ∧ Q.val.right.val t = P.left.val t) := by
  apply same_third_corners
  · exact fun h => Q.val.partner t ((State.value_eq_iff _ _ _).mpr h)
  · exact fun h => P.partner t ((State.value_eq_iff _ _ _).mpr h)
  · exact congrFun Q.property t

noncomputable def bits (P : @Pair A V T X) (Q : P.Group) (t : A) : Bool :=
  decide (Q.val.left.val t = P.right.val t)

theorem group_values (P : @Pair A V T X) (Q : P.Group) (t : A) :
    Q.val.left.value t = (if P.bits Q t then P.right.value t else P.left.value t) ∧
    Q.val.right.value t = (if P.bits Q t then P.left.value t else P.right.value t) := by
  have hn : P.left.val t ≠ P.right.val t := fun h =>
    P.partner t ((State.value_eq_iff _ _ _).mpr h)
  rcases P.group_local Q t with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
    simp [bits, hl, hr, hn, State.value]

theorem bits_invariant (P : @Pair A V T X) (Q : P.Group) (t : A) :
    P.bits Q (P.next t) = P.bits Q t := by
  have h0 := P.group_values Q t
  have h1 := P.group_values Q (P.next t)
  cases ht : P.bits Q t <;> cases hn : P.bits Q (P.next t)
  · rfl
  · simp only [ht, hn, Bool.false_eq_true, ↓reduceIte] at h0 h1
    exact False.elim (P.next_ne t (Q.val.right.value_injective
      (h1.2.trans ((P.value_next t).trans h0.2.symm))))
  · simp only [ht, hn, Bool.false_eq_true, ↓reduceIte] at h0 h1
    exact False.elim (P.next_ne t (Q.val.left.value_injective
      (h1.1.trans ((P.value_next t).trans h0.1.symm))))
  · rfl

noncomputable def orientations [Finite A] (P : @Pair A V T X) (Q : P.Group) :
    CycleClass P.next → Bool := descendCycle (P.bits Q) (P.bits_invariant Q)

@[simp] theorem orient_orientations [Finite A] (P : @Pair A V T X) (Q : P.Group) :
    P.orient (P.orientations Q) = Q := by
  apply Subtype.ext
  apply Pair.ext
  · apply State.ext
    intro t
    change (P.flipLeft (fun t => P.orientations Q (classOf P.next t))
      (fun t => by rw [classOf_apply])).value t = _
    rw [flipLeft_value]
    dsimp [orientations, descendCycle, classOf]
    exact (P.group_values Q t).1.symm
  · apply State.ext
    intro t
    change (P.flipRight (fun t => P.orientations Q (classOf P.next t))
      (fun t => by rw [classOf_apply])).value t = _
    rw [flipRight_value]
    dsimp [orientations, descendCycle, classOf]
    exact (P.group_values Q t).2.symm

@[simp] theorem orientations_orient [Finite A] (P : @Pair A V T X)
    (b : CycleClass P.next → Bool) : P.orientations (P.orient b) = b := by
  funext c
  obtain ⟨t, rfl⟩ := classOf_surjective P.next c
  change P.bits (P.orient b) t = b (classOf P.next t)
  have hn : P.left.val t ≠ P.right.val t := fun h =>
    P.partner t ((State.value_eq_iff _ _ _).mpr h)
  change decide ((if b (classOf P.next t) then P.right.val t else P.left.val t) =
    P.right.val t) = b (classOf P.next t)
  cases b (classOf P.next t) <;> simp [hn]

noncomputable def groupEquiv [Finite A] (P : @Pair A V T X) :
    (CycleClass P.next → Bool) ≃ P.Group where
  toFun := P.orient
  invFun := P.orientations
  left_inv := P.orientations_orient
  right_inv := P.orient_orientations

end Pair
end Barnette.TriangleSystem

end OAI
