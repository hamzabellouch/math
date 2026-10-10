import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic

namespace OAI

/-! # Counting labeled arrangements that respect paired partitions -/

namespace Ostmann

open scoped BigOperators Classical

def PartitionMatching {A B C : Type*} (f : A → C) (g : B → C) :=
  {e : A ≃ B // ∀ a, g (e a) = f a}

noncomputable instance {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) : Fintype (PartitionMatching f g) :=
  inferInstanceAs (Fintype {e : A ≃ B // ∀ a, g (e a) = f a})

def PartitionMatching.restrict {A B C : Type*} {f : A → C} {g : B → C}
    (e : PartitionMatching f g) (c : C) :
    {a : A // f a = c} ≃ {b : B // g b = c} where
  toFun a := ⟨e.1 a, (e.2 a).trans a.2⟩
  invFun b := ⟨e.1.symm b, by rw [← e.2]; simpa using b.2⟩
  left_inv a := Subtype.ext (e.1.symm_apply_apply a)
  right_inv b := Subtype.ext (e.1.apply_symm_apply b)

theorem PartitionMatching.restrict_injective {A B C : Type*}
    {f : A → C} {g : B → C} :
    Function.Injective (fun e : PartitionMatching f g => e.restrict) := by
  intro e e' h
  apply Subtype.ext
  apply Equiv.ext
  intro a
  exact congrArg Subtype.val (Equiv.congr_fun (congrFun h (f a)) ⟨a, rfl⟩)

/-- Each label can be matched independently; an upper bound suffices even
without constructing the inverse assembly map. -/
theorem card_partitionMatching_le {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] (f : A → C) (g : B → C)
    (hcard : ∀ c, Fintype.card {a : A // f a = c} =
      Fintype.card {b : B // g b = c}) :
    Fintype.card (PartitionMatching f g) ≤
      ∏ c, (Fintype.card {a : A // f a = c}).factorial := by
  classical
  calc
    _ ≤ Fintype.card (∀ c, {a : A // f a = c} ≃ {b : B // g b = c}) :=
      Fintype.card_le_of_injective _ PartitionMatching.restrict_injective
    _ = _ := by
      rw [Fintype.card_pi]
      apply Finset.prod_congr rfl
      intro c _
      exact Fintype.card_equiv (Fintype.equivOfCardEq (hcard c))

def slotFiberEquiv {L C : Type*} (f : L → C) (m : ℕ) (c : C) :
    {x : L × Fin m // f x.1 = c} ≃ ({l : L // f l = c} × Fin m) where
  toFun x := (⟨x.1.1, x.2⟩, x.1.2)
  invFun x := ⟨(x.1.1, x.2), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_slotFiber {L C : Type*} [Fintype L]
    (f : L → C) (m : ℕ) (c : C) :
    Fintype.card {x : L × Fin m // f x.1 = c} =
      Fintype.card {l : L // f l = c} * m := by
  classical
  rw [Fintype.card_congr (slotFiberEquiv f m c), Fintype.card_prod, Fintype.card_fin]

/-- Slots and sampled variables remain labeled, so every arrangement is
an actual permutation of all rm positions. -/
theorem card_slotMatching_le {L C : Type*} [Fintype L] [Fintype C]
    (f g : L → C) (m : ℕ)
    (hcard : ∀ c, Fintype.card {l : L // f l = c} =
      Fintype.card {l : L // g l = c}) :
    Fintype.card (PartitionMatching (fun x : L × Fin m => f x.1)
      (fun x : L × Fin m => g x.1)) ≤
      ∏ c, (Fintype.card {l : L // f l = c} * m).factorial := by
  simpa only [card_slotFiber] using
    card_partitionMatching_le (fun x : L × Fin m => f x.1)
      (fun x : L × Fin m => g x.1)
      (fun c => by rw [card_slotFiber, card_slotFiber, hcard c])

end Ostmann

end OAI
