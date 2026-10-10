import OAI.NumberTheory.Ostmann.Construction.DiagonalFactorialBudget
import OAI.NumberTheory.Ostmann.Construction.DiagonalPermutationCountTotal

namespace OAI

open Erdos970

noncomputable section
open scoped Classical
namespace Ostmann.Construction
open DiagonalPermutationCount

theorem remaining_total_normalized_count (m k l : ℕ) (L z : ℝ)
    (hL : 0 < L) (hz : 0 < z) (hmz : (m:ℝ)/L≤z) :
    (Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
      PreservesRemainingBands (remainingTemplate m k l) e}:ℝ)/L^(2^l*m)≤
    (((remainingTemplate m k l).length+1-2^l*m).factorial:ℝ)*
      Real.exp (((2^l:ℕ):ℝ)*m*Real.log (((2^l:ℕ):ℝ)*z)) := by
  have hc : (Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
      PreservesRemainingBands (remainingTemplate m k l) e}:ℝ)≤
      (((remainingTemplate m k l).length+1-2^l*m).factorial:ℝ)*((2^l*m).factorial:ℝ) := by
    exact_mod_cast remaining_total_card_le m k l
  calc
    _ ≤ ((((remainingTemplate m k l).length+1-2^l*m).factorial:ℝ)*((2^l*m).factorial:ℝ))/
        L^(2^l*m) := div_le_div_of_nonneg_right hc (pow_nonneg hL.le _)
    _ = (((remainingTemplate m k l).length+1-2^l*m).factorial:ℝ)*
        (((2^l*m).factorial:ℝ)/L^(2^l*m)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (diagonal_full_factorial_harmonic_gain (2^l) m L z (by positivity) hL hz hmz)
      (Nat.cast_nonneg _)

theorem remaining_transfer_bad_normalized_count (m k l : ℕ) (L z : ℝ)
    (hm : 0 < m) (hL : 0 < L) (hz : 0 < z) (hmz : (m:ℝ)/L≤z) :
    (Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
      PreservesRemainingBands (remainingTemplate m k l) e ∧
        Conclusion.TransferBadArrangement (remainingBulkPermutation m k l e)}:ℝ)/L^(2^l*m)≤
    ((((remainingTemplate m k l).length+1-2^l*m).factorial:ℝ)*
      (((2^l:ℕ):ℝ)^(2*(2^l))))*
      Real.exp ((Real.log z+(1/4:ℝ)*Real.log (((2^l:ℕ):ℝ))+2)*(((2^l:ℕ):ℝ)*m)) := by
  have hc := remaining_transfer_bad_card_le_exp m k l hm
  have hr : (0:ℝ)<((2^l:ℕ):ℝ) := by positivity
  calc
    _ ≤ (((((remainingTemplate m k l).length+1-2^l*m).factorial:ℝ)*
        ((2^l*m).factorial:ℝ))*( ((2^l:ℕ):ℝ)^(2*(2^l))*
        Real.exp ((2-(3/4:ℝ)*Real.log (((2^l:ℕ):ℝ)))*(((2^l:ℕ):ℝ)*m))))/L^(2^l*m) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hL.le _)
      simpa only [Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using hc
    _ = ((((remainingTemplate m k l).length+1-2^l*m).factorial:ℝ)*
        (((2^l:ℕ):ℝ)^(2*(2^l))))*
        ((((2^l*m).factorial:ℝ)/L^(2^l*m))*
          Real.exp ((2-(3/4:ℝ)*Real.log (((2^l:ℕ):ℝ)))*(((2^l:ℕ):ℝ)*m))) := by ring
    _ ≤ ((((remainingTemplate m k l).length+1-2^l*m).factorial:ℝ)*
        (((2^l:ℕ):ℝ)^(2*(2^l))))*
        (Real.exp (((2^l:ℕ):ℝ)*m*Real.log (((2^l:ℕ):ℝ)*z))*
          Real.exp ((2-(3/4:ℝ)*Real.log (((2^l:ℕ):ℝ)))*(((2^l:ℕ):ℝ)*m))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right
        (diagonal_full_factorial_harmonic_gain (2^l) m L z (by positivity) hL hz hmz)
        (Real.exp_pos _).le
    _ = _ := by
      rw [←Real.exp_add,Real.log_mul hr.ne' hz.ne']
      congr 2
      ring

end Ostmann.Construction

end

end OAI
