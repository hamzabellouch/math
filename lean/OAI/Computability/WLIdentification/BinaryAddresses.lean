import OAI.Computability.WLIdentification.CircuitReduction

namespace OAI

namespace WLIdentification

namespace BinaryAddress

abbrev Bits (d : ℕ) := Fin d → Bool

def value : {d : ℕ} → Bits d → ℕ
  | 0, _ => 0
  | _ + 1, v => (if v 0 then 1 else 0) + 2 * value (fun i => v i.succ)

@[simp] theorem value_nil (v : Bits 0) : value v = 0 := rfl
@[simp] theorem value_cons {d : ℕ} (b : Bool) (v : Bits d) :
    value (Fin.cons b v) = (if b then 1 else 0) + 2 * value v := rfl

@[simp] theorem value_zero (d : ℕ) : value (fun _ : Fin d => false) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [value, ih]

@[simp] theorem value_one (d : ℕ) : value (fun _ : Fin d => true) + 1 = 2 ^ d := by
  induction d with
  | zero => simp [value]
  | succ d ih => simp only [value, ↓reduceIte, pow_succ]; omega

theorem value_lt {d : ℕ} (v : Bits d) : value v < 2 ^ d := by
  induction d with
  | zero => simp [value]
  | succ d ih =>
    have h := ih (fun i => v i.succ)
    simp only [value, pow_succ]
    split <;> omega

theorem value_injective (d : ℕ) : Function.Injective (@value d) := by
  induction d with
  | zero => intro v w _; exact Subsingleton.elim _ _
  | succ d ih =>
    intro v w h
    have hh : v 0 = w 0 := by
      cases h1 : v 0 <;> cases h2 : w 0 <;> simp_all [value] <;> omega
    have ht : (fun i : Fin d => v i.succ) = (fun i : Fin d => w i.succ) := by
      apply ih
      simp only [value, hh] at h
      omega
    funext i
    exact Fin.cases hh (fun j => congrFun ht j) i

theorem value_surjective (d : ℕ) (n : ℕ) (hn : n < 2 ^ d) : ∃ v : Bits d, value v = n := by
  induction d generalizing n with
  | zero => refine ⟨Fin.elim0, ?_⟩; simp only [pow_zero] at hn; simp [value]; omega
  | succ d ih =>
    have hdiv : n / 2 < 2 ^ d := by rw [pow_succ] at hn; omega
    obtain ⟨v, hv⟩ := ih (n / 2) hdiv
    refine ⟨Fin.cons (decide (n % 2 = 1)) v, ?_⟩
    simp only [value_cons, hv, decide_eq_true_eq]
    split <;> omega

noncomputable def equiv (d : ℕ) : Bits d ≃ Fin (2 ^ d) :=
  Equiv.ofBijective (fun v => ⟨value v, value_lt v⟩)
    ⟨fun _ _ h => value_injective d (congrArg Fin.val h), fun ⟨n, hn⟩ => by
      obtain ⟨v, hv⟩ := value_surjective d n hn
      exact ⟨v, Fin.ext hv⟩⟩

def negate {d : ℕ} (v : Bits d) : Bits d := fun i => !(v i)

@[simp] theorem negate_negate {d : ℕ} (v : Bits d) : negate (negate v) = v := by
  funext i; exact Bool.not_not _

theorem value_negate {d : ℕ} (v : Bits d) : value (negate v) + value v + 1 = 2 ^ d := by
  induction d with
  | zero => simp [value]
  | succ d ih =>
    have h := ih (fun i => v i.succ)
    change (if !(v 0) then 1 else 0) + 2 * value (negate (fun i => v i.succ)) +
      ((if v 0 then 1 else 0) + 2 * value (fun i => v i.succ)) + 1 = 2 ^ (d + 1)
    rw [pow_succ]
    cases v 0 <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Little-endian carry without converting or enumerating the address space. -/
def advance : {d : ℕ} → Bits d → Bits d
  | 0, v => v
  | _ + 1, v => Fin.cons (!(v 0))
      (if v 0 then advance (fun i => v i.succ) else fun i => v i.succ)

theorem advance_one (d : ℕ) : advance (fun _ : Fin d => true) = fun _ => false := by
  induction d with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [advance]
    · simp [advance, ih]

theorem value_advance {d : ℕ} (v : Bits d) (hv : value v + 1 < 2 ^ d) :
    value (advance v) = value v + 1 := by
  induction d with
  | zero => simp [value] at hv
  | succ d ih =>
    cases hb : v 0 with
    | false => simp [advance, value, hb, Nat.add_comm]
    | true =>
      have ht : value (fun i => v i.succ) + 1 < 2 ^ d := by
        simp only [value, hb, ↓reduceIte, pow_succ] at hv
        omega
      have hit := ih (fun i => v i.succ) ht
      simp only [advance, hb, Bool.not_true, ↓reduceIte, value_cons, Bool.false_eq_true, Nat.zero_add]
      rw [hit]
      simp only [value, hb, ↓reduceIte]
      omega

theorem value_eq_last {d : ℕ} (v : Bits d) : value v + 1 = 2 ^ d ↔ v = fun _ => true := by
  constructor
  · intro h
    apply value_injective d
    have h' := value_one d
    omega
  · rintro rfl; exact value_one d

theorem advance_mod {d : ℕ} (v : Bits d) :
    value (advance v) = (value v + 1) % (2 ^ d) := by
  have h := value_lt v
  by_cases h' : value v + 1 < 2 ^ d
  · rw [value_advance v h', Nat.mod_eq_of_lt h']
  · have he := (value_eq_last v).mp (by omega)
    subst v
    rw [advance_one, value_zero, value_one, Nat.mod_self]

/-- Each carry case fixes just the low prefix, including its first noncarry bit. -/
def Carry {d : ℕ} (h : Fin d) (b : Bool) (v : Bits d) : Prop :=
  (∀ i, i < h → v i = b) ∧ v h = !b

def flipPrefix {d : ℕ} (h : Fin d) (v : Bits d) : Bits d :=
  fun i => if i ≤ h then !(v i) else v i

theorem advance_carry {d : ℕ} (h : Fin d) (v : Bits d) (hv : Carry h true v) :
    advance v = flipPrefix h v := by
  induction d with
  | zero => exact Fin.elim0 h
  | succ d ih =>
    cases h using Fin.cases with
    | zero =>
      have h0 : v 0 = false := hv.2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [advance, flipPrefix]
      · simp [advance, flipPrefix, h0]
    | succ j =>
      have h0 : v 0 = true := hv.1 0 (by simp)
      have ht : Carry j true (fun i => v i.succ) :=
        ⟨fun i hi => hv.1 i.succ (by simpa using hi), hv.2⟩
      funext i
      refine Fin.cases ?_ (fun l => ?_) i
      · simp [advance, flipPrefix]
      · simpa [advance, h0, flipPrefix] using congrFun (ih j _ ht) l

theorem carry_exists {d : ℕ} (v : Bits d) (h : v ≠ fun _ => true) :
    ∃ i, Carry i true v := by
  induction d with
  | zero => exact (h (Subsingleton.elim _ _)).elim
  | succ d ih =>
    cases hb : v 0 with
    | false => exact ⟨0, (by intro i hi; exact (Fin.not_lt_zero _ hi).elim), hb⟩
    | true =>
      have ht : (fun i : Fin d => v i.succ) ≠ fun _ => true := by
        intro he
        apply h
        funext i
        exact Fin.cases hb (fun j => congrFun he j) i
      obtain ⟨i, hi⟩ := ih (fun i => v i.succ) ht
      refine ⟨i.succ, ?_, hi.2⟩
      intro j hj
      cases j using Fin.cases with
      | zero => exact hb
      | succ l => exact hi.1 l (by simpa using hj)

theorem carry_not_last {d : ℕ} {h : Fin d} {v : Bits d} (hv : Carry h true v) :
    value v + 1 < 2 ^ d := by
  have hlt := value_lt v
  by_contra hn
  have he := (value_eq_last v).mp (by omega)
  have hh := hv.2
  rw [he] at hh
  contradiction

end BinaryAddress

namespace BinaryAddress

/-- The executable little-endian digit map; no search through 2^d addresses. -/
def ofNat : (d : ℕ) → ℕ → Bits d
  | 0, _ => Fin.elim0
  | d + 1, n => Fin.cons (decide (n % 2 = 1)) (ofNat d (n / 2))

theorem value_ofNat (d n : ℕ) (h : n < 2 ^ d) : value (ofNat d n) = n := by
  induction d generalizing n with
  | zero => simp only [pow_zero] at h; simp only [ofNat, value_nil]; omega
  | succ d ih =>
    have ht : n / 2 < 2 ^ d := by rw [pow_succ] at h; omega
    simp only [ofNat, value_cons, decide_eq_true_eq, ih _ ht]
    split <;> omega

theorem ofNat_value {d : ℕ} (x : Bits d) : ofNat d (value x) = x :=
  value_injective d (value_ofNat d _ (value_lt x))

@[simp] theorem ofNat_zero (d : ℕ) : ofNat d 0 = fun _ => false :=
  value_injective d (by rw [value_ofNat _ _ (by positivity), value_zero])

end BinaryAddress

namespace ProductMap
variable {r : ℕ}

/-- The relation described by a table, without enumerating its product points. -/
def Rel (D : ProductMap r) (x y : Fin r → Bool) : Prop :=
  (∀ i, x i ∈ D.domain i) ∧ ∀ i, D.mapping i (x i) = y i

theorem rel_point (D : ProductMap r) (a : D.Point) : D.Rel (D.source a) (D.target a) :=
  ⟨fun i => (a i).property, fun _ => rfl⟩

theorem rel_iff (D : ProductMap r) (x y : Fin r → Bool) :
    D.Rel x y ↔ ∃ a : D.Point, D.source a = x ∧ D.target a = y := by
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨fun i => ⟨x i, hx i⟩, rfl, funext hy⟩
  · rintro ⟨a, rfl, rfl⟩; exact rel_point D a

def singleton (x y : Fin r → Bool) : ProductMap r where
  domain i := {x i}
  nonempty i := ⟨x i, by simp⟩
  mapping i _ := y i
  injective i _ hx _ hy _ := (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm

@[simp] theorem singleton_rel (x y u v : Fin r → Bool) :
    (singleton x y).Rel u v ↔ u = x ∧ v = y := by
  simp only [Rel, singleton, Finset.mem_singleton]
  rw [← funext_iff, ← funext_iff, eq_comm (a := y)]

@[simp] theorem identity_rel (x y : Fin r → Bool) : (identity r).Rel x y ↔ x = y := by
  simp [Rel, identity, funext_iff]

def concat {a b : ℕ} (D : ProductMap a) (E : ProductMap b) : ProductMap (a + b) where
  domain := Fin.append D.domain E.domain
  nonempty i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using D.nonempty j
    · simpa only [Fin.append_right] using E.nonempty j
  mapping := Fin.append D.mapping E.mapping
  injective i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using D.injective j
    · simpa only [Fin.append_right] using E.injective j

@[simp] theorem concat_rel {a b : ℕ} (D : ProductMap a) (E : ProductMap b)
    (x y : Fin (a + b) → Bool) :
    (D.concat E).Rel x y ↔
      D.Rel (fun i => x (Fin.castAdd b i)) (fun i => y (Fin.castAdd b i)) ∧
      E.Rel (fun i => x (Fin.natAdd a i)) (fun i => y (Fin.natAdd a i)) := by
  simp only [Rel, concat, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  tauto

def inverse (D : ProductMap r) : ProductMap r where
  domain i := (D.domain i).image (D.mapping i)
  nonempty i := (D.nonempty i).image _
  mapping i b := if false ∈ D.domain i ∧ D.mapping i false = b then false else true
  injective := by
    intro i x hx y hy h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    by_cases he : a = b
    · rw [he]
    · cases a <;> cases b <;> simp_all [D.injective i ha hb]

@[simp] theorem inverse_rel (D : ProductMap r) (x y : Fin r → Bool) :
    D.inverse.Rel x y ↔ D.Rel y x := by
  have h (i : Fin r) (b : Bool) (hb : b ∈ D.domain i) :
      D.inverse.mapping i (D.mapping i b) = b := by
    cases b with
    | false => simp [inverse, hb]
    | true =>
      have hh : ¬ (false ∈ D.domain i ∧ D.mapping i false = D.mapping i true) := by
        rintro ⟨hfalse, he⟩
        have := D.injective i hfalse hb he
        contradiction
      dsimp only [inverse]
      rw [ite_eq_right hh]
  constructor
  · rintro ⟨hx, hy⟩
    have hy' (i : Fin r) : y i ∈ D.domain i ∧ D.mapping i (y i) = x i := by
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (hx i)
      have hh := hy i
      rw [← he, h i a ha] at hh
      exact hh ▸ ⟨ha, he⟩
    exact ⟨fun i => (hy' i).1, fun i => (hy' i).2⟩
  · rintro ⟨hy, hx⟩
    exact ⟨fun i => Finset.mem_image.mpr ⟨y i, hy i, hx i⟩,
      fun i => by rw [← hx i, h i (y i) (hy i)]⟩

end ProductMap

end WLIdentification

end OAI
