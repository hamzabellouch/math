import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Bits
import Mathlib.Logic.Embedding.Basic
import Mathlib.Tactic.FinCases

namespace OAI

namespace BinPackingGap.BinaryRegisterProgram

structure Operands (Reg : Type*) where
  destination : Reg
  left : Reg
  right : Reg
  left_ne_right : left ≠ right
  left_ne_destination : left ≠ destination
  right_ne_destination : right ≠ destination

variable {Reg K : Type*}

def addSlots (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) : Fin 7 ↪ K where
  toFun i := slot (![Sum.inl op.left, Sum.inl op.right, Sum.inr 0, Sum.inr 1,
    Sum.inr 2, Sum.inl op.destination, Sum.inr 3] i)
  inj' := by
    intro i j hij
    have heq := slot.injective hij
    fin_cases i <;> fin_cases j <;>
      simp_all [op.left_ne_right, op.left_ne_destination, op.right_ne_destination,
        Ne.symm op.left_ne_right, Ne.symm op.left_ne_destination,
        Ne.symm op.right_ne_destination]

@[simp] theorem addSlots_zero (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 0 = slot (Sum.inl op.left) := rfl

@[simp] theorem addSlots_one (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 1 = slot (Sum.inl op.right) := rfl

@[simp] theorem addSlots_two (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 2 = slot (Sum.inr 0) := rfl

@[simp] theorem addSlots_three (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 3 = slot (Sum.inr 1) := rfl

@[simp] theorem addSlots_four (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 4 = slot (Sum.inr 2) := rfl

@[simp] theorem addSlots_five (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 5 = slot (Sum.inl op.destination) := rfl

@[simp] theorem addSlots_six (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 6 = slot (Sum.inr 3) := rfl

def mulSlots (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) : Fin 9 ↪ K where
  toFun i := slot (![Sum.inl op.left, Sum.inl op.right, Sum.inl op.destination,
    Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5] i)
  inj' := by
    intro i j hij
    have heq := slot.injective hij
    fin_cases i <;> fin_cases j <;>
      simp_all [op.left_ne_right, op.left_ne_destination, op.right_ne_destination,
        Ne.symm op.left_ne_right, Ne.symm op.left_ne_destination,
        Ne.symm op.right_ne_destination]

@[simp] theorem mulSlots_zero (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 0 = slot (Sum.inl op.left) := rfl

@[simp] theorem mulSlots_one (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 1 = slot (Sum.inl op.right) := rfl

@[simp] theorem mulSlots_two (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 2 = slot (Sum.inl op.destination) := rfl

@[simp] theorem mulSlots_three (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 3 = slot (Sum.inr 0) := rfl

@[simp] theorem mulSlots_four (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 4 = slot (Sum.inr 1) := rfl

@[simp] theorem mulSlots_five (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 5 = slot (Sum.inr 2) := rfl

@[simp] theorem mulSlots_six (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 6 = slot (Sum.inr 3) := rfl

@[simp] theorem mulSlots_seven (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 7 = slot (Sum.inr 4) := rfl

@[simp] theorem mulSlots_eight (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 8 = slot (Sum.inr 5) := rfl

def registerWords (values : Reg → ℕ) : Reg ⊕ Fin 6 → List Bool
  | Sum.inl r => (values r).bits
  | Sum.inr _ => []

@[simp] theorem registerWords_reg (values : Reg → ℕ) (r : Reg) :
    registerWords values (Sum.inl r) = (values r).bits := rfl

@[simp] theorem registerWords_scratch (values : Reg → ℕ) (i : Fin 6) :
    registerWords values (Sum.inr i) = [] := rfl

noncomputable def registerTapes (slot : (Reg ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : Reg → ℕ) : K → List Bool := by
  classical
  exact fun k =>
    if h : ∃ i, slot i = k then registerWords values (Classical.choose h) else base k

@[simp] theorem registerTapes_slot (slot : (Reg ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : Reg → ℕ) (i : Reg ⊕ Fin 6) :
    registerTapes slot base values (slot i) = registerWords values i := by
  unfold registerTapes
  rw [dite_eq_left ⟨i, rfl⟩]
  congr 1
  exact slot.injective (Classical.choose_spec (show ∃ j, slot j = slot i from ⟨i, rfl⟩))

@[simp] theorem registerTapes_reg (slot : (Reg ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : Reg → ℕ) (r : Reg) :
    registerTapes slot base values (slot (Sum.inl r)) = (values r).bits :=
  registerTapes_slot slot base values (Sum.inl r)

@[simp] theorem registerTapes_scratch (slot : (Reg ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : Reg → ℕ) (i : Fin 6) :
    registerTapes slot base values (slot (Sum.inr i)) = [] :=
  registerTapes_slot slot base values (Sum.inr i)

theorem registerTapes_other (slot : (Reg ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : Reg → ℕ) (k : K)
    (hk : ¬ ∃ i, slot i = k) : registerTapes slot base values k = base k := by
  simp [registerTapes, hk]

theorem registerTapes_update [DecidableEq Reg] [DecidableEq K]
    (slot : (Reg ⊕ Fin 6) ↪ K) (base : K → List Bool) (values : Reg → ℕ)
    (d : Reg) (v : ℕ) :
    Function.update (registerTapes slot base values) (slot (Sum.inl d)) v.bits =
      registerTapes slot base (Function.update values d v) := by
  funext k
  by_cases hk : ∃ j, slot j = k
  · obtain ⟨j, rfl⟩ := hk
    cases j with
    | inl r =>
      by_cases hrd : r = d
      · subst r; simp
      · have hslot : slot (Sum.inl r) ≠ slot (Sum.inl d) :=
          slot.injective.ne (by simpa only [ne_eq, Sum.inl.injEq] using hrd)
        simp [Function.update_of_ne, hrd, hslot]
    | inr i =>
      have hslot : slot (Sum.inr i) ≠ slot (Sum.inl d) := slot.injective.ne (by simp)
      simp [Function.update_of_ne, hslot]
  · have hslot : k ≠ slot (Sum.inl d) := fun h => hk ⟨Sum.inl d, h.symm⟩
    simp [Function.update_of_ne hslot, registerTapes_other slot base _ k hk]

theorem registerTapes_mul_workspace (slot : (Reg ⊕ Fin 6) ↪ K)
    (op : Operands Reg) (base : K → List Bool) (values : Reg → ℕ)
    (i : Fin 9) (hi : 3 ≤ i.val) :
    registerTapes slot base values (mulSlots slot op i) = [] := by
  fin_cases i <;> simp_all

theorem registerTapes_add_workspace (slot : (Reg ⊕ Fin 6) ↪ K)
    (op : Operands Reg) (base : K → List Bool) (values : Reg → ℕ)
    (i : Fin 7) (hi : 2 ≤ i.val) (hout : i ≠ 5) :
    registerTapes slot base values (addSlots slot op i) = [] := by
  fin_cases i <;> simp_all

end BinPackingGap.BinaryRegisterProgram

noncomputable section

namespace BinPackingGap.PackingRegisterFrame

open BinaryRegisterProgram

variable {Local Global K : Type}

def withScratch (register : Local ↪ Global) : (Local ⊕ Fin 6) ↪ (Global ⊕ Fin 6) where
  toFun
    | .inl r => .inl (register r)
    | .inr i => .inr i
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all only [Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl]
    exact register.injective h

def localSlots (slot : (Global ⊕ Fin 6) ↪ K) (register : Local ↪ Global) :
    (Local ⊕ Fin 6) ↪ K := (withScratch register).trans slot

@[simp] theorem localSlots_reg (slot : (Global ⊕ Fin 6) ↪ K)
    (register : Local ↪ Global) (r : Local) :
    localSlots slot register (.inl r) = slot (.inl (register r)) := rfl

@[simp] theorem localSlots_scratch (slot : (Global ⊕ Fin 6) ↪ K)
    (register : Local ↪ Global) (i : Fin 6) :
    localSlots slot register (.inr i) = slot (.inr i) := rfl

theorem registerTapes_eq_self (slot : (Local ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : Local → Nat)
    (shape : ∀ i, base (slot i) = registerWords values i) :
    registerTapes slot base values = base := by
  funext k
  by_cases hk : ∃ i, slot i = k
  · obtain ⟨i, rfl⟩ := hk
    rw [registerTapes_slot, shape]
  · exact registerTapes_other slot base values k hk

theorem restrict (slot : (Global ⊕ Fin 6) ↪ K) (register : Local ↪ Global)
    (base : K → List Bool) (values : Global → Nat) :
    registerTapes (localSlots slot register) (registerTapes slot base values)
      (values ∘ register) = registerTapes slot base values := by
  apply registerTapes_eq_self
  intro i
  cases i <;> simp [Function.comp_def]

theorem replace (slot : (Global ⊕ Fin 6) ↪ K) (register : Local ↪ Global)
    (base : K → List Bool) (before after : Global → Nat) (localAfter : Local → Nat)
    (inside : ∀ r, after (register r) = localAfter r)
    (outside : ∀ r, (¬ ∃ l, register l = r) → after r = before r) :
    registerTapes (localSlots slot register) (registerTapes slot base before) localAfter =
      registerTapes slot base after := by
  funext k
  by_cases hk : ∃ i, slot i = k
  · obtain ⟨i, rfl⟩ := hk
    cases i with
    | inl r =>
        by_cases hr : ∃ l, register l = r
        · obtain ⟨l, rfl⟩ := hr
          change registerTapes (localSlots slot register) _ localAfter
            (localSlots slot register (.inl l)) = _
          simp only [registerTapes_reg, inside]
        · have hlocal : ¬ ∃ i, localSlots slot register i = slot (.inl r) := by
            rintro ⟨i, hi⟩
            have h := slot.injective hi
            cases i with
            | inl l => exact hr ⟨l, Sum.inl.inj h⟩
            | inr j => cases h
          rw [registerTapes_other _ _ _ _ hlocal, registerTapes_reg,
            registerTapes_reg, outside r hr]
    | inr j =>
        change registerTapes (localSlots slot register) _ localAfter
          (localSlots slot register (.inr j)) = _
        simp only [registerTapes_scratch]
  · have hlocal : ¬ ∃ i, localSlots slot register i = k := by
      rintro ⟨i, hi⟩
      exact hk ⟨withScratch register i, hi⟩
    rw [registerTapes_other _ _ _ _ hlocal, registerTapes_other _ _ _ _ hk,
      registerTapes_other _ _ _ _ hk]

theorem external_update [DecidableEq K] (slot : (Global ⊕ Fin 6) ↪ K) (base : K → List Bool)
    (values : Global → Nat) (output : K) (outside : ∀ i, slot i ≠ output)
    (word : List Bool) :
    registerTapes slot (Function.update base output word) values =
      Function.update (registerTapes slot base values) output word := by
  funext k
  by_cases hk : k = output
  · subst k
    have hn : ¬ ∃ i, slot i = output := by rintro ⟨i, hi⟩; exact outside i hi
    simp [registerTapes_other _ _ _ _ hn]
  · by_cases hs : ∃ i, slot i = k
    · obtain ⟨i, rfl⟩ := hs
      simp [outside i]
    · simp [registerTapes_other _ _ _ _ hs, hk]

end BinPackingGap.PackingRegisterFrame

end

end OAI
