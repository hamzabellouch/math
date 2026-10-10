import OAI.Combinatorics.EditApproximation.Binary.BinaryEnvelopeReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundedKernel
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Rounded canonical actions and their acceptance guards retain the
literal initial-table reads used by each child-envelope computation. -/

namespace EditApproximation
namespace BinaryFraction



theorem roundedBandReadWithWork_eq_cost {n M : ℕ} (exponent b : ℕ)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (roundedBandReadWithWork exponent b band hne read).1 =
      (roundedBandWithWork exponent b band hne (fun i q => (read i q).1)).1 ∧
    (roundedBandReadWithWork exponent b band hne read).2 ≤
      (roundedBandWithWork exponent b band hne (fun i q => (read i q).1)).2 + M * (band.length * (R + 3)) := by
  have add_cost (a b s t e D : ℕ) (h : a ≤ b + D) :
      a + s + t + e + 3 ≤ b + s + t + e + 3 + D := by omega
  apply vectorMapWithWork_extra
  · intro i
    simp only [bandEnvelopeReadWithWork_eq]
  · intro i
    have h := bandEnvelopeReadWithWork_cost b band read i R (fun _ _ => hr i _)
    dsimp only
    simp only [bandEnvelopeReadWithWork_eq]
    exact add_cost _ _ _ _ _ _ h



theorem unskippedGuardReadWithWork_eq_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (b exponent : ℕ) (F : BinaryFraction)
    (band wide : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (unskippedGuardReadWithWork parent center b exponent F band wide hne read).1 =
      (unskippedGuardWithWork parent center b exponent F band wide hne (fun i q => (read i q).1)).1 ∧
    (unskippedGuardReadWithWork parent center b exponent F band wide hne read).2 ≤
      (unskippedGuardWithWork parent center b exponent F band wide hne (fun i q => (read i q).1)).2 +
        M * (band.length * (R + 3)) + M * (band.length * (R + 3)) := by
  have he := envelopeVectorReadWithWork_eq_cost b band read R hr
  have hrnd := roundedBandReadWithWork_eq_cost exponent b band hne read R hr
  unfold unskippedGuardReadWithWork unskippedGuardWithWork
  dsimp only
  rw [he.1, hrnd.1]
  exact ⟨rfl, by omega⟩

end BinaryFraction
end EditApproximation

end OAI
