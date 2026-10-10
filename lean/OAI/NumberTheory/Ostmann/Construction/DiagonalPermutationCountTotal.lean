import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCounts
import OAI.NumberTheory.Ostmann.Conclusion.LowLevelBadPairs
import OAI.NumberTheory.Ostmann.Construction.DiagonalPermutationCount

namespace OAI

open Erdos970

noncomputable section
open scoped Classical
namespace Ostmann.Construction.DiagonalPermutationCount

theorem remaining_total_card_le (m k l : ℕ) :
    Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
      PreservesRemainingBands (remainingTemplate m k l) e} ≤
      ((remainingTemplate m k l).length+1-2^l*m).factorial * (2^l*m).factorial := by
  have h := full_bulk_property_card_le (remainderBulkPositionEquiv m k l) (fun _ => True)
  simpa only [and_true,Subtype.range_coe_subtype, Nat.card_eq_fintype_card,
    Fintype.card_subtype_true,Fintype.card_perm,Fintype.card_prod,Fintype.card_fin,
    remainder_nonbulk_card] using h

theorem remaining_nonbulk_card_le (m k l : ℕ) :
    Fintype.card (NonbulkPosition (remainingTemplate m k l)) ≤ 1+2^l*(6+4*k) := by
  have h := Arithmetic.HistorySymbolicEncoding.template_current_length_le (Template.initial m k) l
  have hr : (remainingTemplate m k l).length ≤
      (Template.current (Template.initial m k) l).length := List.length_filter_le _ _
  rw [InitialCoordinatesTemplate.initial_length] at h
  rw [remainder_nonbulk_card]
  have hs : (remainingTemplate m k l).length ≤ 2^l*m+2^l*(6+4*k) := by
    nlinarith
  omega

theorem remaining_transfer_bad_card_le (m k l : ℕ) :
    Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
      PreservesRemainingBands (remainingTemplate m k l) e ∧
        Conclusion.TransferBadArrangement (remainingBulkPermutation m k l e)} ≤
      ((remainingTemplate m k l).length+1-2^l*m).factorial *
        Conclusion.transferBadCount (2^l) m := by
  simpa only [remainingBulkPermutation,remainder_nonbulk_card,Conclusion.transferBadCount] using
    full_bulk_property_card_le (remainderBulkPositionEquiv m k l) Conclusion.TransferBadArrangement

theorem remaining_transfer_bad_card_le_exp (m k l : ℕ) (hm : 0 < m) :
    (Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
      PreservesRemainingBands (remainingTemplate m k l) e ∧
        Conclusion.TransferBadArrangement (remainingBulkPermutation m k l e)} : ℝ) ≤
      (((remainingTemplate m k l).length+1-2^l*m).factorial : ℝ) *
        ((2^l*m).factorial : ℝ) * (((2^l : ℕ) : ℝ)^(2*(2^l)) *
          Real.exp ((2-(3/4:ℝ)*Real.log (2^l))*((2^l:ℕ):ℝ)*m)) := by
  have h := remaining_transfer_bad_card_le m k l
  have h' : (Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
      PreservesRemainingBands (remainingTemplate m k l) e ∧
        Conclusion.TransferBadArrangement (remainingBulkPermutation m k l e)} : ℝ) ≤
      (((remainingTemplate m k l).length+1-2^l*m).factorial : ℝ) *
        (Conclusion.transferBadCount (2^l) m : ℝ) := by exact_mod_cast h
  have hb := Conclusion.transferBad_fraction_bound (r := 2^l) (by positivity) hm
  have hb' := (div_le_iff₀ (show (0:ℝ)<((2^l*m).factorial:ℝ) by positivity)).mp hb
  refine h'.trans ?_
  convert mul_le_mul_of_nonneg_left hb' (show (0:ℝ)≤
    (((remainingTemplate m k l).length+1-2^l*m).factorial:ℝ) by positivity) using 1;
    push_cast; ring

end Ostmann.Construction.DiagonalPermutationCount

end

end OAI
