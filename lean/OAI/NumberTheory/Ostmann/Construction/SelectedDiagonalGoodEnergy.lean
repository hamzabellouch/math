import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalGoodSum
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalNormalizer

namespace OAI

open Erdos970

noncomputable section
open scoped Classical
namespace Ostmann.Construction
namespace InitialSourceChoice
open Conclusion DiagonalPermutationCount
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem diagonalGoodPermutation_card_le_total (m k l : ℕ) :
    Nat.card {e // diagonalGoodPermutation m k l e}≤
      Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
        PreservesRemainingBands (remainingTemplate m k l) e} := by
  let f : {e // diagonalGoodPermutation m k l e} →
      {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
        PreservesRemainingBands (remainingTemplate m k l) e} := fun e => ⟨e.val,e.property.1⟩
  apply Nat.card_le_card_of_injective f
  intro e g h
  apply Subtype.ext
  have hval := congrArg (fun z : {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
      PreservesRemainingBands (remainingTemplate m k l) e} => z.val) h
  exact hval

theorem selectedGoodCovarianceSum_normalized_le (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s : ℕ) (X : ℝ) (l : ℕ) (ε : ℝ) (hε : 0≤ε)
    (hgood : ∀e,diagonalGoodPermutation (2*(bulkSize k L/2)) k l e →
      ‖C.selectedDiagonalCovariance spectator s X l e‖≤ε) :
    C.selectedDiagonalNormalizer l*(C.selectedGoodCovarianceSum spectator s X l).re≤
      (C.selectedDiagonalNormalizer l*
        (Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate (2*(bulkSize k L/2)) k l)) //
          PreservesRemainingBands (remainingTemplate (2*(bulkSize k L/2)) k l) e}:ℝ))*ε := by
  have hcard : (Nat.card {e // diagonalGoodPermutation (2*(bulkSize k L/2)) k l e}:ℝ)≤
      (Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate (2*(bulkSize k L/2)) k l)) //
        PreservesRemainingBands (remainingTemplate (2*(bulkSize k L/2)) k l) e}:ℝ) := by
    exact_mod_cast diagonalGoodPermutation_card_le_total (2*(bulkSize k L/2)) k l
  calc
    _ ≤ C.selectedDiagonalNormalizer l*‖C.selectedGoodCovarianceSum spectator s X l‖ :=
      mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (C.selectedDiagonalNormalizer_nonneg _)
    _ ≤ C.selectedDiagonalNormalizer l*
        ((Nat.card {e // diagonalGoodPermutation (2*(bulkSize k L/2)) k l e}:ℝ)*ε) :=
      mul_le_mul_of_nonneg_left (C.selectedGoodCovarianceSum_norm_le spectator s X l ε hgood)
        (C.selectedDiagonalNormalizer_nonneg _)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hε)
        (C.selectedDiagonalNormalizer_nonneg _)

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
