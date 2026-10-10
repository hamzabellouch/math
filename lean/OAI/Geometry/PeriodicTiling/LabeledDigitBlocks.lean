import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases

namespace OAI

universe uK uA uB uL uR uJ uF

namespace PeriodicTilingThree

structure LabeledBlocks (K : Type uK) (A : Type uA) (B : Type uB) (a b : ℕ) where
  decode : K ≃ ((A × ZMod a) ⊕ (B × ZMod b))

namespace LabeledBlocks

variable {K : Type uK} {A : Type uA} {B : Type uB} {a b : ℕ}

def labelRotation (t : ℤ) : Equiv.Perm ((A × ZMod a) ⊕ (B × ZMod b)) where
  toFun
    | .inl (c, y) => .inl (c, y + (t : ZMod a))
    | .inr (c, y) => .inr (c, y + (t : ZMod b))
  invFun
    | .inl (c, y) => .inl (c, y - (t : ZMod a))
    | .inr (c, y) => .inr (c, y - (t : ZMod b))
  left_inv := by rintro (⟨c, y⟩ | ⟨c, y⟩) <;> simp
  right_inv := by rintro (⟨c, y⟩ | ⟨c, y⟩) <;> simp

def C (D : LabeledBlocks K A B a b) (x : K) : ZMod a × ZMod b :=
  match D.decode x with
  | .inl (_, y) => (y, 0)
  | .inr (_, y) => (0, y)

def T (D : LabeledBlocks K A B a b) (t : ℤ) : Equiv.Perm K :=
  D.decode.trans ((labelRotation t).trans D.decode.symm)

def blockId (D : LabeledBlocks K A B a b) (x : K) : A ⊕ B :=
  match D.decode x with
  | .inl (c, _) => .inl c
  | .inr (c, _) => .inr c

def block (D : LabeledBlocks K A B a b) (c : A ⊕ B) : Set K :=
  {x | D.blockId x = c}

theorem unique_block (D : LabeledBlocks K A B a b) (x : K) :
    ∃! c : A ⊕ B, x ∈ D.block c := by
  exact ⟨D.blockId x, rfl, fun c hc => hc.symm⟩

noncomputable def blockEquivA (D : LabeledBlocks K A B a b) (c : A) :
    {x : K // x ∈ D.block (.inl c)} ≃ ZMod a :=
  (Equiv.ofBijective
    (fun y : ZMod a => (⟨D.decode.symm (.inl (c, y)), by simp [block, blockId]⟩ :
      {x : K // x ∈ D.block (.inl c)}))
    (by
      constructor
      · intro y z h
        have hh := congrArg (fun x => D.decode x.val) h
        simpa using hh
      · rintro ⟨x, hx⟩
        cases h : D.decode x with
        | inl z =>
            have hz : z.1 = c := by simpa [block, blockId, h] using hx
            refine ⟨z.2, Subtype.ext ?_⟩
            apply D.decode.injective
            rw [Equiv.apply_symm_apply, h]
            exact congrArg Sum.inl (Prod.ext hz.symm rfl)
        | inr z => simp [block, blockId, h] at hx)).symm

noncomputable def blockEquivB (D : LabeledBlocks K A B a b) (c : B) :
    {x : K // x ∈ D.block (.inr c)} ≃ ZMod b :=
  (Equiv.ofBijective
    (fun y : ZMod b => (⟨D.decode.symm (.inr (c, y)), by simp [block, blockId]⟩ :
      {x : K // x ∈ D.block (.inr c)}))
    (by
      constructor
      · intro y z h
        have hh := congrArg (fun x => D.decode x.val) h
        simpa using hh
      · rintro ⟨x, hx⟩
        cases h : D.decode x with
        | inl z => simp [block, blockId, h] at hx
        | inr z =>
            have hz : z.1 = c := by simpa [block, blockId, h] using hx
            refine ⟨z.2, Subtype.ext ?_⟩
            apply D.decode.injective
            rw [Equiv.apply_symm_apply, h]
            exact congrArg Sum.inr (Prod.ext hz.symm rfl))).symm

@[simp] theorem C_decode_symm_inl (D : LabeledBlocks K A B a b)
    (c : A) (y : ZMod a) : D.C (D.decode.symm (.inl (c, y))) = (y, 0) := by
  simp [C]

@[simp] theorem C_decode_symm_inr (D : LabeledBlocks K A B a b)
    (c : B) (y : ZMod b) : D.C (D.decode.symm (.inr (c, y))) = (0, y) := by
  simp [C]

@[simp] theorem decode_T (D : LabeledBlocks K A B a b) (t : ℤ) (x : K) :
    D.decode (D.T t x) = labelRotation t (D.decode x) := by
  simp [T]

@[simp] theorem T_decode_symm_inl (D : LabeledBlocks K A B a b)
    (t : ℤ) (c : A) (y : ZMod a) :
    D.T t (D.decode.symm (.inl (c, y))) =
      D.decode.symm (.inl (c, y + (t : ZMod a))) := by
  simp [T, labelRotation]

@[simp] theorem T_decode_symm_inr (D : LabeledBlocks K A B a b)
    (t : ℤ) (c : B) (y : ZMod b) :
    D.T t (D.decode.symm (.inr (c, y))) =
      D.decode.symm (.inr (c, y + (t : ZMod b))) := by
  simp [T, labelRotation]

@[simp] theorem blockId_T (D : LabeledBlocks K A B a b) (t : ℤ) (x : K) :
    D.blockId (D.T t x) = D.blockId x := by
  unfold blockId
  rw [decode_T]
  cases D.decode x <;> rfl

@[simp] theorem T_zero (D : LabeledBlocks K A B a b) (x : K) : D.T 0 x = x := by
  apply D.decode.injective
  rw [decode_T]
  cases h : D.decode x with
  | inl z => simp [labelRotation]
  | inr z => simp [labelRotation]

theorem T_add (D : LabeledBlocks K A B a b) (t u : ℤ) (x : K) :
    D.T (t + u) x = D.T t (D.T u x) := by
  apply D.decode.injective
  simp only [decode_T]
  cases h : D.decode x with
  | inl z => simp [labelRotation, add_comm, add_left_comm]
  | inr z => simp [labelRotation, add_comm, add_left_comm]

@[simp] theorem T_neg_T (D : LabeledBlocks K A B a b) (t : ℤ) (x : K) :
    D.T (-t) (D.T t x) = x := by
  rw [← T_add]
  simp

@[simp] theorem T_T_neg (D : LabeledBlocks K A B a b) (t : ℤ) (x : K) :
    D.T t (D.T (-t) x) = x := by
  rw [← T_add]
  simp

def transport {L : Type uL} (D : LabeledBlocks K A B a b) (e : L ≃ K) :
    LabeledBlocks L A B a b := ⟨e.trans D.decode⟩

@[simp] theorem C_transport {L : Type uL} (D : LabeledBlocks K A B a b)
    (e : L ≃ K) (x : L) : (D.transport e).C x = D.C (e x) := rfl

def copyRight (D : LabeledBlocks K A B a b) (R : Type uR) :
    LabeledBlocks (K × R) (A × R) (B × R) a b where
  decode :=
    { toFun := fun x => match D.decode x.1 with
        | .inl (c, y) => .inl ((c, x.2), y)
        | .inr (c, y) => .inr ((c, x.2), y)
      invFun := fun x => match x with
        | .inl ((c, r), y) => (D.decode.symm (.inl (c, y)), r)
        | .inr ((c, r), y) => (D.decode.symm (.inr (c, y)), r)
      left_inv := by
        rintro ⟨x, r⟩
        cases h : D.decode x with
        | inl z => simpa [h] using congrArg (fun w => (w, r)) (D.decode.symm_apply_apply x)
        | inr z => simpa [h] using congrArg (fun w => (w, r)) (D.decode.symm_apply_apply x)
      right_inv := by
        rintro (⟨⟨c, r⟩, y⟩ | ⟨⟨c, r⟩, y⟩) <;> simp }

@[simp] theorem C_copyRight (D : LabeledBlocks K A B a b) (R : Type uR) (x : K × R) :
    (D.copyRight R).C x = D.C x.1 := by
  rcases x with ⟨x, r⟩
  cases h : D.decode x <;> simp [C, copyRight, h]

@[simp] theorem T_copyRight (D : LabeledBlocks K A B a b) (R : Type uR) (t : ℤ)
    (x : K × R) : (D.copyRight R).T t x = (D.T t x.1, x.2) := by
  rcases x with ⟨x, r⟩
  cases h : D.decode x with
  | inl z => simp [T, copyRight, labelRotation, h]
  | inr z => simp [T, copyRight, labelRotation, h]

noncomputable def digit (a b r A B : ℕ) [NeZero a] [NeZero b] [NeZero r]
    (h : r = A * a + B * b) : LabeledBlocks (ZMod r) (Fin A) (Fin B) a b where
  decode := Fintype.equivOfCardEq (by
    simp only [ZMod.card, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    exact h)

theorem C_nonconstant (D : LabeledBlocks K A B a b) [Nonempty K]
    [Nontrivial (ZMod a)] [Nontrivial (ZMod b)] :
    ∃ x y : K, D.C x ≠ D.C y := by
  obtain ⟨x⟩ := ‹Nonempty K›
  cases h : D.decode x with
  | inl z =>
      refine ⟨D.decode.symm (.inl (z.1, 0)), D.decode.symm (.inl (z.1, 1)), ?_⟩
      rw [C_decode_symm_inl, C_decode_symm_inl]
      intro he
      exact zero_ne_one (congrArg Prod.fst he)
  | inr z =>
      refine ⟨D.decode.symm (.inr (z.1, 0)), D.decode.symm (.inr (z.1, 1)), ?_⟩
      rw [C_decode_symm_inr, C_decode_symm_inr]
      intro he
      exact zero_ne_one (congrArg Prod.snd he)

section Coordinate

variable {J : Type uJ} [DecidableEq J] (F : J → Type uF) (j : J)
variable {a b : ℕ} {A : Type uA} {B : Type uB}

def onCoordinate (D : LabeledBlocks (F j) A B a b) :
    LabeledBlocks (∀ q, F q)
      (A × (∀ q : {q // q ≠ j}, F q))
      (B × (∀ q : {q // q ≠ j}, F q)) a b :=
  (D.copyRight (∀ q : {q // q ≠ j}, F q)).transport (Equiv.piSplitAt j F)

@[simp] theorem C_onCoordinate (D : LabeledBlocks (F j) A B a b) (x : ∀ q, F q) :
    (onCoordinate F j D).C x = D.C (x j) := by
  simp [onCoordinate]

theorem C_eq_of_coordinate_eq (D : LabeledBlocks (F j) A B a b)
    {x y : ∀ q, F q} (h : x j = y j) :
    (onCoordinate F j D).C x = (onCoordinate F j D).C y := by
  simp only [C_onCoordinate, h]

theorem C_designated_witness (D : LabeledBlocks (F j) A B a b)
    [∀ q, Nonempty (F q)] [Nontrivial (ZMod a)] [Nontrivial (ZMod b)] :
    ∃ x y : ∀ q, F q, (∀ q, q ≠ j → x q = y q) ∧
      (onCoordinate F j D).C x ≠ (onCoordinate F j D).C y := by
  classical
  obtain ⟨u, v, huv⟩ := D.C_nonconstant
  let base : ∀ q, F q := fun q => Classical.choice (inferInstance : Nonempty (F q))
  refine ⟨Function.update base j u, Function.update base j v, ?_, ?_⟩
  · intro q hq
    simp [Function.update_of_ne hq]
  · simpa only [C_onCoordinate, Function.update_self] using huv

theorem C_active_iff (D : LabeledBlocks (F j) A B a b)
    [∀ q, Nonempty (F q)] [Nontrivial (ZMod a)] [Nontrivial (ZMod b)] (q : J) :
    (∃ x y : ∀ r, F r, (∀ r, r ≠ q → x r = y r) ∧
      (onCoordinate F j D).C x ≠ (onCoordinate F j D).C y) ↔ q = j := by
  constructor
  · rintro ⟨x, y, hxy, hne⟩
    by_contra hq
    exact hne (C_eq_of_coordinate_eq F j D (hxy j (Ne.symm hq)))
  · intro hq
    subst q
    exact C_designated_witness F j D

end Coordinate

end LabeledBlocks

end PeriodicTilingThree

end OAI
