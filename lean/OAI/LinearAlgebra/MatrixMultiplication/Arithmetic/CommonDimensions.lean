import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
import Mathlib.Data.Fintype.Pi

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CommonDimensions

variable {K H : Type*} [CommSemiring K] [Fintype H] [DecidableEq H]

def familyProduct {X Y Z : H → Type*} (T : ∀ h, Tensor K (X h) (Y h) (Z h)) :
    Tensor K (∀ h, X h) (∀ h, Y h) (∀ h, Z h) :=
  fun x y z => ∏ h, T h (x h) (y h) (z h)

def pairWords (A B : H → Type*) :
    ((∀ h, A h) × (∀ h, B h)) ≃ (∀ h, A h × B h) where
  toFun x h := (x.1 h, x.2 h)
  invFun x := (fun h => (x h).1, fun h => (x h).2)
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq H] in
theorem matrix_familyProduct (A B C : H → Type*)
    [∀ h, DecidableEq (A h)] [∀ h, DecidableEq (B h)] [∀ h, DecidableEq (C h)] :
    Tensor.pullback (pairWords A B) (pairWords B C) (pairWords C A)
      (familyProduct (fun h => Tensor.matrixCoefficients (K := K) (A h) (B h) (C h))) =
      Tensor.matrixCoefficients (∀ h, A h) (∀ h, B h) (∀ h, C h) := by
  classical
  funext x y z
  simp only [Tensor.pullback, pairWords, familyProduct, Tensor.matrixCoefficients,
    Equiv.coe_fn_mk]
  by_cases h : x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i _
    exact ite_eq_left ⟨congrFun h.1 i, congrFun h.2.1 i, congrFun h.2.2 i⟩
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, x.2 i = y.1 i ∧ y.2 i = z.1 i ∧ z.2 i = x.1 i := by
      intro hi
      exact h ⟨funext (fun i => (hi i).1), funext (fun i => (hi i).2.1),
        funext (fun i => (hi i).2.2)⟩
    obtain ⟨i, hi⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

theorem matrix_familyProduct_restrict (A B C : H → Type*)
    [∀ h, Fintype (A h)] [∀ h, Fintype (B h)] [∀ h, Fintype (C h)]
    [∀ h, DecidableEq (A h)] [∀ h, DecidableEq (B h)] [∀ h, DecidableEq (C h)] :
    ∃ (a : ((∀ h, A h) × (∀ h, B h)) → (∀ h, A h × B h) → K)
      (b : ((∀ h, B h) × (∀ h, C h)) → (∀ h, B h × C h) → K)
      (c : ((∀ h, C h) × (∀ h, A h)) → (∀ h, C h × A h) → K),
      Tensor.restrict a b c
        (familyProduct (fun h => Tensor.matrixCoefficients (K := K) (A h) (B h) (C h))) =
        Tensor.matrixCoefficients (∀ h, A h) (∀ h, B h) (∀ h, C h) := by
  classical
  refine ⟨(fun x s => if s = pairWords A B x then 1 else 0),
    (fun y s => if s = pairWords B C y then 1 else 0),
    (fun z s => if s = pairWords C A z then 1 else 0), ?_⟩
  rw [← Tensor.pullback_eq_restrict]
  exact matrix_familyProduct A B C

theorem dimension_card (a : H → ℕ) :
    Fintype.card (∀ h, Fin (a h)) = ∏ h, a h := by simp

theorem volume_card (a b c : H → ℕ) :
    Fintype.card (∀ h, Fin (a h)) * Fintype.card (∀ h, Fin (b h)) *
      Fintype.card (∀ h, Fin (c h)) = ∏ h, a h * b h * c h := by
  simp [Finset.prod_mul_distrib]

theorem common_oriented_dimensions {S : Type*}
    (a b c : S → H → ℕ) (a₀ b₀ c₀ : H → ℕ)
    (ha : ∀ s h, a s h = a₀ h) (hb : ∀ s h, b s h = b₀ h)
    (hc : ∀ s h, c s h = c₀ h) (s : S) :
    (Fintype.card (∀ h, Fin (a s h)), Fintype.card (∀ h, Fin (b s h)),
      Fintype.card (∀ h, Fin (c s h))) =
    (∏ h, a₀ h, ∏ h, b₀ h, ∏ h, c₀ h) := by
  simp [ha, hb, hc]

end MatrixMultiplication.CommonDimensions

end OAI
