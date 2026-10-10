import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsDivisibility
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReductionLocal

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceForwardBGuards
open Construction HistorySignedDecode HistoryOccurrenceVariables HistorySupportReduction

theorem signedPivot_eq_of_supported {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    signedPivot ⟨a.frequency,a.giantPlus,a.giantMinus,a.small⟩
      left.root.frequency right.root.frequency u hp hm=(p:ℤ) := by
  have hu : ((u.map SmallSlot.value).prod:ℤ)≠0 := by
    exact_mod_cast (History.supported_compensation_product_pos hs).ne'
  have hd := mul_ne_zero (History.supported_root_frequency_ne_zero hs) hu
  have hr := History.supported_reversal hs
  simp only [Nat.cast_mul] at hr
  dsimp only [signedPivot]
  rw [hr]
  exact Int.mul_ediv_cancel_left _ hd

theorem rebuild_integralGuard_of_supported {l : ℕ} (h : History l)
    {V : ℕ→ℕ} {outside : List ℕ} (hs : h.Supported V outside) :
    (rebuild h h.root.giantPlus h.root.giantMinus).IntegralGuard := by
  induction h with
  | leaf a => trivial
  | node a p u hp hm left right il ir =>
    have hu : ((u.map SmallSlot.value).prod:ℤ)≠0 := by
      exact_mod_cast (History.supported_compensation_product_pos hs).ne'
    obtain ⟨hlp,hrp,hlm,hrm⟩ := History.supported_child_giants hs
    change (rebuild (.node a p u hp hm left right) (a.giantPlus:ℤ) (a.giantMinus:ℤ)).IntegralGuard
    simp only [rebuild,SignedHistory.IntegralGuard,rebuild_root,
      signedPivot_eq_of_supported hs]
    refine ⟨mul_ne_zero (History.supported_root_frequency_ne_zero hs) hu,?_,?_,?_⟩
    · exact ⟨(p:ℤ),by simpa only [Nat.cast_mul] using History.supported_reversal hs⟩
    · simpa only [hlp,hlm] using il (History.supported_left hs)
    · simpa only [hrp,hrm] using ir (History.supported_right hs)

theorem actual_divisible_of_supported {l : ℕ} (h : History l)
    {V : ℕ→ℕ} {outside : List ℕ} (hs : h.Supported V outside) (i : InternalKey h) :
    ((internalSlot h i).value:ℤ) ∣
      HistorySignedNumerators.actual h h.root.giantPlus h.root.giantMinus i :=
  HistorySignedNumerators.actual_divisible h _ _ (rebuild_integralGuard_of_supported h hs) i

theorem actual_square_not_dvd_of_supported {l : ℕ} (h : History l)
    {V : ℕ→ℕ} {outside : List ℕ} (hs : h.Supported V outside)
    (hlarge : LargePrimes V h) (i : InternalKey h) :
    ¬((internalSlot h i).value:ℤ)^2 ∣
      HistorySignedNumerators.actual h h.root.giantPlus h.root.giantMinus i := by
  induction h with
  | leaf a => exact Empty.elim i
  | node a p u hp hm left right il ir =>
    obtain ⟨hlp,hrp,hlm,hrm⟩ := History.supported_child_giants hs
    change ¬((internalSlot (.node a p u hp hm left right) i).value:ℤ)^2 ∣
      HistorySignedNumerators.actual (.node a p u hp hm left right) (a.giantPlus:ℤ) (a.giantMinus:ℤ) i
    rcases i with i | i | i
    · have ht := (localTests_of_supported_node hs hlarge.2.1).2.2.1
        (u.get i) (List.get_mem _ _)
      simpa only [internalSlot,Sum.elim_inl,HistorySignedNumerators.actual_node,
        pow_two,Nat.cast_mul] using ht
    · simpa only [internalSlot,Sum.elim_inr,Sum.elim_inl,HistorySignedNumerators.actual_node,
        signedPivot_eq_of_supported hs,hlp,hlm] using
        il (History.supported_left hs) hlarge.2.2.1 i
    · simpa only [internalSlot,Sum.elim_inr,HistorySignedNumerators.actual_node,
        signedPivot_eq_of_supported hs,hrp,hrm] using
        ir (History.supported_right hs) hlarge.2.2.2 i

theorem ownPrimeTests_of_supported {l : ℕ} (h : History l)
    {V : ℕ→ℕ} {outside : List ℕ} (hs : h.Supported V outside)
    (hlarge : LargePrimes V h) :
    (rebuild h h.root.giantPlus h.root.giantMinus).IntegralGuard ∧
      ∀i:InternalKey h,
        ((internalSlot h i).value:ℤ) ∣
          HistorySignedNumerators.actual h h.root.giantPlus h.root.giantMinus i ∧
        ¬((internalSlot h i).value:ℤ)^2 ∣
          HistorySignedNumerators.actual h h.root.giantPlus h.root.giantMinus i :=
  ⟨rebuild_integralGuard_of_supported h hs,fun i =>
    ⟨actual_divisible_of_supported h hs i,actual_square_not_dvd_of_supported h hs hlarge i⟩⟩

end Ostmann.Arithmetic.HistoryBulkReferenceForwardBGuards

end

end OAI
