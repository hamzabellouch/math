import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsInsertion

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction Characters.RationalHistory ClearedCoefficientFlags MvPolynomial
open HistoryOccurrenceVariables HistoryPairPattern HistoryPairRows HistoryPairGiantCoordinates
open HistoryBulkReferenceTests HistoryCRTIntegration HistoryOccurrenceRows
open HistorySymbolicScope HistoryCoefficientBounds HistoryRepeatedRenaming
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

theorem flag_vars_not_giant (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (i : Occurrences h k) :
    (∀j∈(leftFlag h k hs ks i).vars,j∉giantCoordinates h k) ∧
    (∀j∈(rightFlag h k hs ks i).vars,j∉giantCoordinates h k) := by
  classical
  let lev : PairKey h k → ℕ := fun j => if j∈giantCoordinates h k then 0 else l+1
  have hl : ∀j,lev (leftMap h k j)=rootFreeLevel h j := by
    intro j
    rcases j with b | j
    · simp only [lev,giant_mem,ite_true,rootFreeLevel,Sum.elim_inl]
    · simp only [lev,left_small_not_mem,ite_false,rootFreeLevel,Sum.elim_inr]
  have hr : ∀j,lev (rightMap h k j)=rootFreeLevel k j := by
    intro j
    rcases j with b | j
    · rw [←shared_giant]
      simp only [lev,giant_mem,ite_true,rootFreeLevel,Sum.elim_inl]
    · simp only [lev,right_small_not_mem,ite_false,rootFreeLevel,Sum.elim_inr]
  have ha : Above lev (level h k i) (row h k hs ks i).1 ∧
      Above lev (level h k i) (row h k hs ks i).2 := by
    rcases i with i | i
    · have hf := rows_above h hs _ _ (rootFreeLevel h)
        (coefficientHistory_rootFreeAbove h hs false)
        (coefficientHistory_rootFreeAbove h hs true) i
      exact ⟨(above_rename _ _ _ _ hl _).mpr hf.1,(above_rename _ _ _ _ hl _).mpr hf.2⟩
    · have hf := rows_above k ks _ _ (rootFreeLevel k)
        (coefficientHistory_rootFreeAbove k ks false)
        (coefficientHistory_rootFreeAbove k ks true) i
      exact ⟨(above_rename _ _ _ _ hr _).mpr hf.1,(above_rename _ _ _ _ hr _).mpr hf.2⟩
  have hf := coefficients_above lev (level h k i) _ _ ha.1 ha.2
  constructor
  · intro j hj hg
    have hh := hf.1 j hj
    simp only [lev,hg,ite_true,Nat.not_lt_zero] at hh
  · intro j hj hg
    have hh := hf.2.1 j hj
    simp only [lev,hg,ite_true,Nat.not_lt_zero] at hh

theorem flags_eval_eq_off_giants (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v w : PairKey h k→ℤ) (hvw : ∀j,j∉giantCoordinates h k→v j=w j)
    (i : Occurrences h k) :
    eval v (leftFlag h k hs ks i)=eval w (leftFlag h k hs ks i) ∧
    eval v (rightFlag h k hs ks i)=eval w (rightFlag h k hs ks i) := by
  constructor
  · apply eval₂Hom_congr' rfl _ rfl
    intro j hj _
    exact hvw j ((flag_vars_not_giant h k hs ks i).1 j hj)
  · apply eval₂Hom_congr' rfl _ rfl
    intro j hj _
    exact hvw j ((flag_vars_not_giant h k hs ks i).2 j hj)

theorem primeResidueIndicatorAt_eq_off_giants (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v w : PairKey h k→ℤ) (hvw : ∀j,j∉giantCoordinates h k→v j=w j)
    (z : ZMod (representativeModulus h k)×ZMod (representativeModulus h k)) :
    primeResidueIndicatorAt h k hs ks v z=primeResidueIndicatorAt h k hs ks w z := by
  have he : finiteOwnPrimeLinesAt h k hs ks v z ↔ finiteOwnPrimeLinesAt h k hs ks w z := by
    unfold finiteOwnPrimeLinesAt ownPrimeLineAt ownPrimeSquareLineAt
    simp only [(flags_eval_eq_off_giants h k hs ks v w hvw _).1,
      (flags_eval_eq_off_giants h k hs ks v w hvw _).2]
  unfold primeResidueIndicatorAt
  rw [he]

theorem orderedSourceIndicatorB_eq_fixed_giants (sources : SourceFamily) (m k₀ : ℕ)
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (x : SourceAssignment sources (Template.current (Template.initial m k₀) l))
    (Xp Xm : ℤ) :
    orderedSourceIndicatorB sources m k₀ h k hs ks hh x Xp Xm =
      primeResidueIndicatorAt h k hs ks
        (integerInsertOrderedGiants m k₀ h k hs hh
          (orderedIntegerSourceValues sources m k₀ l x) (fun _=>0)) (Xp,Xm) := by
  apply primeResidueIndicatorAt_eq_off_giants
  intro j hj
  simp only [integerInsertOrderedGiants,dite_eq_right hj]

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
