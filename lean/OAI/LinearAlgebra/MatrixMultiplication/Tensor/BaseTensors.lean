import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.ComplexCWPrimitiveDegeneration

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace BaseTwo

def tensor : Tensor ℂ (Fin 2) (Fin 2) (Fin 2) :=
  fun x y z => if x.val + y.val + z.val = 1 then 1 else 0

def flagB (x : Fin 2) : Prop := x = 1
def flagA (z : Fin 2) : Prop := z = 1
def flagC (y : Fin 2) : Prop := y = 1

theorem support_iff (x y z : Fin 2) :
    tensor x y z ≠ 0 ↔
      (x = 1 ∧ y = 0 ∧ z = 0) ∨
      (x = 0 ∧ y = 0 ∧ z = 1) ∨ (x = 0 ∧ y = 1 ∧ z = 0) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num [Fin.ext_iff, Prod.mk.injEq, tensor]

theorem one_hot (x y z : Fin 2) (hs : tensor x y z ≠ 0) :
    (if flagB x then 1 else 0) + (if flagA z then 1 else 0) +
      (if flagC y then 1 else 0) = (1 : ℕ) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagB, flagA, flagC] at hs <;>
      norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagB, flagA, flagC]

theorem conditionalB (x y z : Fin 2) :
    tensor x y z ≠ 0 ∧ flagB x ↔ x = 1 ∧ y = 0 ∧ z = 0 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagB]

theorem conditionalA (x y z : Fin 2) :
    tensor x y z ≠ 0 ∧ flagA z ↔ x = 0 ∧ y = 0 ∧ z = 1 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagA]

theorem conditionalC (x y z : Fin 2) :
    tensor x y z ≠ 0 ∧ flagC y ↔ x = 0 ∧ y = 1 ∧ z = 0 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagC]

def point : Fin 3 → Fin 2 × Fin 2 × Fin 2
  | 0 => (1, 0, 0)
  | 1 => (0, 0, 1)
  | 2 => (0, 1, 0)

theorem point_injective : Function.Injective point := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp only [point, Prod.mk.injEq, Fin.ext_iff] at h <;> norm_num at h <;> norm_num

theorem point_supported (i : Fin 3) :
    tensor (point i).1 (point i).2.1 (point i).2.2 = 1 := by
  fin_cases i <;> norm_num [Fin.ext_iff, Prod.mk.injEq, point, tensor]

theorem support_enumeration (x y z : Fin 2) :
    tensor x y z ≠ 0 ↔ ∃ i, point i = (x, y, z) := by
  rw [support_iff]
  constructor
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp [point, Prod.mk.injEq] at hi <;> rcases hi with ⟨rfl, rfl, rfl⟩ <;>
      simp

theorem tensor_eq_sum (x y z : Fin 2) :
    tensor x y z = ∑ i, if point i = (x, y, z) then (1 : ℂ) else 0 := by
  simp only [Fin.sum_univ_three, point, Prod.mk.injEq, Fin.ext_iff]
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [tensor, Fin.sum_univ_succ, point, Prod.mk.injEq, Fin.ext_iff]

theorem color_masses (p : Fin 3 → ℝ) :
    (∑ i, if flagB (point i).1 then p i else 0) = p 0 ∧
    (∑ i, if flagA (point i).2.2 then p i else 0) = p 1 ∧
    (∑ i, if flagC (point i).2.1 then p i else 0) = p 2 := by
  simp only [Fin.sum_univ_three]
  norm_num [point, flagB, flagA, flagC, Fin.ext_iff]

end BaseTwo

namespace BaseThree

def tensor : Tensor ℂ (Fin 3) (Fin 3) (Fin 3) := CWBoundary.tensor

def flagB (x : Fin 3) : Prop := x ≠ 0
def flagA (z : Fin 3) : Prop := z ≠ 0
def flagC (y : Fin 3) : Prop := y = 2

theorem support_iff (x y z : Fin 3) :
    tensor x y z ≠ 0 ↔
      (x = 0 ∧ y = 0 ∧ z = 2) ∨ (x = 0 ∧ y = 1 ∧ z = 1) ∨
      (x = 2 ∧ y = 0 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 0) ∨
      (x = 0 ∧ y = 2 ∧ z = 0) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, CWBoundary.tensor, CoppersmithWinograd.tensor]

theorem one_hot (x y z : Fin 3) (hs : tensor x y z ≠ 0) :
    (if flagB x then 1 else 0) + (if flagA z then 1 else 0) +
      (if flagC y then 1 else 0) = (1 : ℕ) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, CWBoundary.tensor, CoppersmithWinograd.tensor,
      flagB, flagA, flagC] at hs <;>
      norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, CWBoundary.tensor, CoppersmithWinograd.tensor,
        flagB, flagA, flagC]

theorem conditionalA (x y z : Fin 3) :
    tensor x y z ≠ 0 ∧ flagA z ↔
      x = 0 ∧ ((y = 0 ∧ z = 2) ∨ (y = 1 ∧ z = 1)) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, CWBoundary.tensor, CoppersmithWinograd.tensor, flagA]

theorem conditionalB (x y z : Fin 3) :
    tensor x y z ≠ 0 ∧ flagB x ↔
      z = 0 ∧ ((x = 2 ∧ y = 0) ∨ (x = 1 ∧ y = 1)) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, CWBoundary.tensor, CoppersmithWinograd.tensor, flagB]

theorem conditionalC (x y z : Fin 3) :
    tensor x y z ≠ 0 ∧ flagC y ↔ x = 0 ∧ y = 2 ∧ z = 0 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, CWBoundary.tensor, CoppersmithWinograd.tensor, flagC]

theorem readableA (x y z : Fin 3) (hs : tensor x y z ≠ 0) (ha : flagA z) :
    (y = 0 ↔ z = 2) := by
  rcases (conditionalA x y z).mp ⟨hs, ha⟩ with ⟨rfl, h | h⟩ <;>
    rcases h with ⟨rfl, rfl⟩ <;> norm_num [Fin.ext_iff]

theorem readableB (x y z : Fin 3) (hs : tensor x y z ≠ 0) (hb : flagB x) :
    (x = 2 ↔ y = 0) := by
  rcases (conditionalB x y z).mp ⟨hs, hb⟩ with ⟨rfl, h | h⟩ <;>
    rcases h with ⟨rfl, rfl⟩ <;> norm_num [Fin.ext_iff]

def point : Fin 5 → Fin 3 × Fin 3 × Fin 3
  | 0 => (0, 0, 2)
  | 1 => (0, 1, 1)
  | 2 => (2, 0, 0)
  | 3 => (1, 1, 0)
  | 4 => (0, 2, 0)

theorem point_injective : Function.Injective point := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp only [point, Prod.mk.injEq, Fin.ext_iff] at h <;> norm_num at h <;> norm_num

theorem point_supported (i : Fin 5) :
    tensor (point i).1 (point i).2.1 (point i).2.2 = 1 := by
  fin_cases i <;> norm_num [Fin.ext_iff, Prod.mk.injEq, point, tensor, CWBoundary.tensor, CoppersmithWinograd.tensor]

theorem support_enumeration (x y z : Fin 3) :
    tensor x y z ≠ 0 ↔ ∃ i, point i = (x, y, z) := by
  rw [support_iff]
  constructor
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp [point, Prod.mk.injEq] at hi <;> rcases hi with ⟨rfl, rfl, rfl⟩ <;>
      simp

theorem tensor_eq_sum (x y z : Fin 3) :
    tensor x y z = ∑ i, if point i = (x, y, z) then (1 : ℂ) else 0 := by
  simp only [Fin.sum_univ_five, point, Prod.mk.injEq, Fin.ext_iff]
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [tensor, CWBoundary.tensor, CoppersmithWinograd.tensor,
      Fin.sum_univ_succ, point, Prod.mk.injEq, Fin.ext_iff]

theorem color_masses (p : Fin 5 → ℝ) :
    (∑ i, if flagB (point i).1 then p i else 0) = p 2 + p 3 ∧
    (∑ i, if flagA (point i).2.2 then p i else 0) = p 0 + p 1 ∧
    (∑ i, if flagC (point i).2.1 then p i else 0) = p 4 := by
  simp only [Fin.sum_univ_five]
  norm_num [point, flagB, flagA, flagC, Fin.ext_iff]

end BaseThree
end MatrixMultiplication

end

end OAI
