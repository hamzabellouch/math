import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequencyForward
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequencyPermutation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequency
open Construction Conclusion HistoryFrequencyResidues HistoryBulkResidueNormSum
open HistoryBulkSpectatorReferenceRaw HistoryBulkSupportConverse

theorem independentRTest_source_eq_reference_of_fullPermutation
    (K m k l : ℕ) (sources : SourceFamily) (V : ℕ→ℕ)
    (old old' : History l) (a a' : State)
    (c c' : HistoryChoices sources (Template.initial m k) V l)
    (x y : SourceAssignment sources (Template.current (Template.initial m k) l))
    (π : Equiv.Perm (Fin (Template.current (Template.initial m k) l).length))
    (hπ : ∀i,((Template.current (Template.initial m k) l).get i).role=.bulk ↔
      ((Template.current (Template.initial m k) l).get (π i)).role=.bulk)
    (hvalues : ∀i,(y i).val=(x (π i)).val)
    (hx : a.small=assignedSlots sources (Template.current (Template.initial m k) l) x)
    (hy : a'.small=assignedSlots sources (Template.current (Template.initial m k) l) y)
    {outside : List ℕ} (hs : old.Supported V outside) (hs' : old'.Supported V outside)
    (hmass : (assignmentPrior sources (Template.current (Template.initial m k) l)).mass x≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j))
    (z : ZMod ((pairedFrequencyProduct old old')^(K+2)) ×
      ZMod ((pairedFrequencyProduct old old')^(K+2))) :
    independentRTest K old old' (inducedBulkPermutation m k l π hπ) z
      (sourceBulkUnits ((pairedFrequencyProduct old old')^(K+2)) sources m k l x)=
    independentReferenceIndicator K old old'
      (decodeHistory sources (Template.initial m k) V l a c)
      (decodeHistory sources (Template.initial m k) V l a' c') z :=
  independentRTest_source_eq_reference_of_mass K m k l sources V old old' a a' c c' x y
    (inducedBulkPermutation m k l π hπ) hx hy
    (bulkSamples_fullPermutation sources m k l π hπ x y hvalues) hs hs' hmass hfreq z

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequency

end

end OAI
