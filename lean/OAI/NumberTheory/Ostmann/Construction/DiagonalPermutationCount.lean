import OAI.NumberTheory.Ostmann.Construction.DiagonalPermutationCountPositions

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction.DiagonalPermutationCount

def fullBulkRestriction {T : List SourceSlot} {r m : ℕ}
    (E : BulkPosition T ≃ Fin r × Fin m) (e : Equiv.Perm (RemainingIndex T)) :
    Equiv.Perm (Fin r × Fin m) :=
  if h : PreservesRemainingBands T e then orderedBulkRestriction E ⟨e,h⟩ else Equiv.refl _

theorem full_bulk_property_card_le {T : List SourceSlot} {r m : ℕ}
    (E : BulkPosition T ≃ Fin r × Fin m) (Bad : Equiv.Perm (Fin r × Fin m) → Prop) :
    Nat.card {e : Equiv.Perm (RemainingIndex T) //
      PreservesRemainingBands T e ∧ Bad (fullBulkRestriction E e)} ≤
      (Fintype.card (NonbulkPosition T)).factorial *
        Nat.card {σ : Equiv.Perm (Fin r × Fin m) // Bad σ} := by
  let f : {e : Equiv.Perm (RemainingIndex T) //
      PreservesRemainingBands T e ∧ Bad (fullBulkRestriction E e)} →
      {e : BandPermutation T // Bad (orderedBulkRestriction E e)} :=
    fun e => ⟨⟨e.val,e.property.1⟩,by
      simpa only [fullBulkRestriction,dite_eq_left e.property.1] using e.property.2⟩
  have hf : Function.Injective f := by
    intro e g h
    apply Subtype.ext
    exact congrArg (fun x => x.val.val) h
  exact (Nat.card_le_card_of_injective f hf).trans (ordered_bulk_property_card_le E Bad)

def remainingBulkPermutation (m k l : ℕ)
    (e : Equiv.Perm (RemainingIndex (remainingTemplate m k l))) :
    Equiv.Perm (Fin (2^l) × Fin m) :=
  fullBulkRestriction (remainderBulkPositionEquiv m k l) e

theorem remainingBulkPermutation_apply (m k l : ℕ)
    (e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)))
    (he : PreservesRemainingBands (remainingTemplate m k l) e)
    (u : Fin (2^l) × Fin m) :
    ((remainderBulkPositionEquiv m k l).symm (remainingBulkPermutation m k l e u)).val =
      e (((remainderBulkPositionEquiv m k l).symm u).val) := by
  simp only [remainingBulkPermutation,fullBulkRestriction,dite_eq_left he,
    orderedBulkRestriction,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

theorem remaining_bulk_fiber_card_le (m k l : ℕ) (σ : Equiv.Perm (Fin (2^l) × Fin m)) :
    Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
      PreservesRemainingBands (remainingTemplate m k l) e ∧
        remainingBulkPermutation m k l e = σ} ≤
      ((remainingTemplate m k l).length+1-2^l*m).factorial := by
  have h := full_bulk_property_card_le (remainderBulkPositionEquiv m k l) (fun τ => τ=σ)
  simpa only [remainingBulkPermutation,remainder_nonbulk_card,Nat.card_unique,Nat.mul_one] using h

theorem remaining_bad_card_le (m k l : ℕ) :
    Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
      PreservesRemainingBands (remainingTemplate m k l) e ∧
        Conclusion.BadArrangement (remainingBulkPermutation m k l e)} ≤
      ((remainingTemplate m k l).length+1-2^l*m).factorial *
        Conclusion.badArrangementCount (2^l) m := by
  simpa only [remainingBulkPermutation,remainder_nonbulk_card,Conclusion.badArrangementCount] using
    full_bulk_property_card_le (remainderBulkPositionEquiv m k l) Conclusion.BadArrangement

theorem remaining_bad_card_le_exp (m k l : ℕ) (hm : 0 < m) :
    (Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
      PreservesRemainingBands (remainingTemplate m k l) e ∧
        Conclusion.BadArrangement (remainingBulkPermutation m k l e)} : ℝ) ≤
      (((remainingTemplate m k l).length+1-2^l*m).factorial : ℝ) *
        (((2^l : ℕ) : ℝ)^(2*(2^l)) * ((m.factorial : ℝ)^(2^l) *
          Real.exp ((Real.log (2^l)+1)*((2^l : ℕ) : ℝ)*m/4))) := by
  have h := remaining_bad_card_le m k l
  have h' : (Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate m k l)) //
      PreservesRemainingBands (remainingTemplate m k l) e ∧
        Conclusion.BadArrangement (remainingBulkPermutation m k l e)} : ℝ) ≤
      (((remainingTemplate m k l).length+1-2^l*m).factorial : ℝ) *
        (Conclusion.badArrangementCount (2^l) m : ℝ) := by exact_mod_cast h
  refine h'.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using
    Conclusion.badArrangementCount_le (r := 2^l) (by positivity) hm

end Ostmann.Construction.DiagonalPermutationCount

end

end OAI
