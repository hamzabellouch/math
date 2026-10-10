import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsAncestors
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesValues
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportPlan
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportRowsCoefficients

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction Construction.CanonicalOccurrenceTransport Characters.RationalHistory
open HistorySymbolicStep HistorySignedDecode HistorySignedNumerators

lemma select_range {A : Type} (d : A) (xs : List A) :
    select d (List.range xs.length) xs=xs := by
  apply List.ext_getElem
  · simp [select]
  · intro i hi hj
    simp [select,hj]

lemma eval_product {Index : Type*} (es : List (Expr Index)) (x : Index→ℚ) (xs : List SmallSlot)
    (he : es.map (fun e => e.rationalEval x)=xs.map (fun a => (a.value:ℚ))) :
    (product es).rationalEval x=((xs.map SmallSlot.value).prod:ℚ) := by
  rw [product_eval,he]
  simp only [List.map_map,Function.comp_def,Nat.cast_list_prod]

theorem pivot_eval_signed {Index : Type*} (s v w Xp Xm : ℤ) (sm u hp hm : List SmallSlot)
    (p m : Expr Index) (ue hpe hme : List (Expr Index)) (x : Index→ℚ)
    (hpv : p.rationalEval x=(Xp:ℚ)) (hmv : m.rationalEval x=(Xm:ℚ))
    (hu : ue.map (fun e => e.rationalEval x)=u.map (fun a => (a.value:ℚ)))
    (hhp : hpe.map (fun e => e.rationalEval x)=hp.map (fun a => (a.value:ℚ)))
    (hhm : hme.map (fun e => e.rationalEval x)=hm.map (fun a => (a.value:ℚ)))
    (hd : s*((u.map SmallSlot.value).prod:ℤ) ≠ 0)
    (hi : s*((u.map SmallSlot.value).prod:ℤ) ∣
      reversalNumerator v w (Xp*((hp.map SmallSlot.value).prod:ℤ))
        (Xm*((hm.map SmallSlot.value).prod:ℤ))) :
    (pivot s v w p m ue hpe hme).rationalEval x=
      (signedPivot ⟨s,Xp,Xm,sm⟩ v w u hp hm:ℚ) := by
  rw [pivot_eval,hpv,hmv,eval_product _ _ _ hu,eval_product _ _ _ hhp,
    eval_product _ _ _ hhm]
  have hdz : (s:ℚ)*((u.map SmallSlot.value).prod:ℚ)≠0 := by
    have hz : ((s*((u.map SmallSlot.value).prod:ℤ):ℤ):ℚ)≠0 := Int.cast_ne_zero.mpr hd
    simpa only [Int.cast_mul,Int.cast_natCast] using hz
  apply (div_eq_iff hdz).mpr
  have he := congrArg (fun z : ℤ => (z:ℚ))
    (signedPivot_reversal ⟨s,Xp,Xm,sm⟩ v w u hp hm hi)
  simpa only [reversalNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast,mul_comm]
    using he

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI
