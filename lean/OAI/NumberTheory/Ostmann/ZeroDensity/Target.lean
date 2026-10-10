import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Ostmann.ZeroDensity

def PrimitiveFamily (Q : ℕ) :=
  Σ q : Fin Q, {χ : DirichletCharacter ℂ (q.val + 1) // χ.IsPrimitive}

instance (Q : ℕ) : Fintype (PrimitiveFamily Q) := by
  classical
  unfold PrimitiveFamily
  infer_instance

instance (Q : ℕ) : DecidableEq (PrimitiveFamily Q) := Classical.decEq _

theorem card_primitiveFamily_le (Q : ℕ) : Fintype.card (PrimitiveFamily Q) ≤ Q ^ 2 := by
  classical
  change Fintype.card (Σ q : Fin Q,
    {χ : DirichletCharacter ℂ (q.val + 1) // χ.IsPrimitive}) ≤ Q ^ 2
  rw [Fintype.card_sigma]
  calc
    ∑ q : Fin Q, Fintype.card {χ : DirichletCharacter ℂ (q.val + 1) // χ.IsPrimitive} ≤
        ∑ q : Fin Q, Fintype.card (DirichletCharacter ℂ (q.val + 1)) := by
      apply Finset.sum_le_sum
      intro q _
      exact Fintype.card_subtype_le _
    _ = ∑ q : Fin Q, (q.val + 1).totient := by
      apply Finset.sum_congr rfl
      intro q _
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (q.val + 1)
    _ ≤ ∑ _q : Fin Q, Q := by
      apply Finset.sum_le_sum
      intro q _
      exact (Nat.totient_le _).trans (by omega)
    _ = Q ^ 2 := by simp [pow_two]

def smoothError {q : ℕ} (χ : DirichletCharacter ℂ q) (φ : ℝ → ℝ) (X : ℝ) : ℂ := by
  classical
  exact (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n * (φ ((n : ℝ) / X) : ℂ)) -
    if χ = 1 then ((X * ∫ t in Set.Ioi (0 : ℝ), φ t : ℝ) : ℂ) else 0

def totalPrimitiveError (Q : ℕ) (exception : Option (PrimitiveFamily Q))
    (φ : ℝ → ℝ) (X : ℝ) : ℝ := by
  classical
  exact ∑ χ : PrimitiveFamily Q,
    if some χ = exception then 0 else ‖smoothError χ.2.1 φ X‖

theorem totalPrimitiveError_nonneg (Q : ℕ) (exception : Option (PrimitiveFamily Q))
    (φ : ℝ → ℝ) (X : ℝ) : 0 ≤ totalPrimitiveError Q exception φ X := by
  classical
  unfold totalPrimitiveError
  exact Finset.sum_nonneg fun χ _ => by split <;> positivity

theorem totalPrimitiveError_none (Q : ℕ) (φ : ℝ → ℝ) (X : ℝ) :
    totalPrimitiveError Q none φ X =
      ∑ χ : PrimitiveFamily Q, ‖smoothError χ.2.1 φ X‖ := by
  classical
  simp [totalPrimitiveError]

theorem totalPrimitiveError_some (Q : ℕ) (exception : PrimitiveFamily Q)
    (φ : ℝ → ℝ) (X : ℝ) :
    totalPrimitiveError Q (some exception) φ X =
      ∑ χ ∈ Finset.univ.erase exception, ‖smoothError χ.2.1 φ X‖ := by
  classical
  simp [totalPrimitiveError, Finset.sum_ite, Finset.filter_ne']

end Ostmann.ZeroDensity

end

end OAI
