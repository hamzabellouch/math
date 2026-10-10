import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequencyBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequency
open Construction Conclusion CanonicalHistoryLeafBulk

def inducedBulkPermutation (m k l : ℕ)
    (π : Equiv.Perm (Fin (Template.current (Template.initial m k) l).length))
    (hπ : ∀i,((Template.current (Template.initial m k) l).get i).role=.bulk ↔
      ((Template.current (Template.initial m k) l).get (π i)).role=.bulk) :
    Equiv.Perm (Fin (2^l)×Fin m) :=
  (currentBulkPositionEquiv m k l).symm.trans
    ((π.subtypePerm (fun i=> (hπ i).symm)).trans (currentBulkPositionEquiv m k l))

theorem inducedBulkPermutation_position (m k l : ℕ)
    (π : Equiv.Perm (Fin (Template.current (Template.initial m k) l).length))
    (hπ : ∀i,((Template.current (Template.initial m k) l).get i).role=.bulk ↔
      ((Template.current (Template.initial m k) l).get (π i)).role=.bulk)
    (u : Fin (2^l)×Fin m) :
    ((currentBulkPositionEquiv m k l).symm (inducedBulkPermutation m k l π hπ u)).val=
      π ((currentBulkPositionEquiv m k l).symm u).val := by
  simp only [inducedBulkPermutation,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

theorem bulkSamples_fullPermutation (sources : SourceFamily) (m k l : ℕ)
    (π : Equiv.Perm (Fin (Template.current (Template.initial m k) l).length))
    (hπ : ∀i,((Template.current (Template.initial m k) l).get i).role=.bulk ↔
      ((Template.current (Template.initial m k) l).get (π i)).role=.bulk)
    (x y : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hvalues : ∀i,(y i).val=(x (π i)).val) (u : Fin (2^l)×Fin m) :
    bulkSamples sources m k l y u.1 u.2=
      bulkSamples sources m k l x (inducedBulkPermutation m k l π hπ u).1
        (inducedBulkPermutation m k l π hπ u).2 := by
  unfold bulkSamples
  rw [hvalues]
  exact (congrArg (fun i=>(x i).val) (inducedBulkPermutation_position m k l π hπ u)).symm

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequency

end

end OAI
