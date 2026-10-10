import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsFrequencySource

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequency
open Construction Conclusion HistoryBulkProducts HistoryFrequencyResidues
open HistoryPairedFrequencyAverageHaar HistoryBulkSpectatorReferenceRaw CanonicalHistoryLeafBulk
open HistoryBulkResidueNormSum HistoryBulkSupportConverse HistoryBulkReferenceTestsFrequency

theorem frequencyLeaves_decode_slots_related
    (M m k l : ℕ) (sources : SourceFamily) (V : ℕ→ℕ)
    (a : State) (c : HistoryChoices sources (Template.initial m k) V l)
    (x y : SourceAssignment sources (Template.current (Template.initial m k) l))
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (hy : a.small=assignedSlots sources (Template.current (Template.initial m k) l) y)
    (hbulk : ∀u : Fin (2^l)×Fin m,
      bulkSamples sources m k l y u.1 u.2=bulkSamples sources m k l x (σ u).1 (σ u).2)
    (samples : Fin (2^l)×Fin m → (ZMod M)ˣ)
    (hsamples : ∀u,(samples u:ZMod M)=(bulkSamples sources m k l x u.1 u.2:ZMod M)) :
    frequencyLeaves M (decodeHistory sources (Template.initial m k) V l a c)=
      bulkLeaves m l (fun u=>samples (σ u)) := by
  apply frequencyLeaves_decode_slots M sources m k V l a c y hy (fun u=>samples (σ u))
  intro u
  rw [hsamples,hbulk]

theorem independentRTest_source_eq_reference_of_mass
    (K m k l : ℕ) (sources : SourceFamily) (V : ℕ→ℕ)
    (old old' : History l) (a a' : State)
    (c c' : HistoryChoices sources (Template.initial m k) V l)
    (x y : SourceAssignment sources (Template.current (Template.initial m k) l))
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (hx : a.small=assignedSlots sources (Template.current (Template.initial m k) l) x)
    (hy : a'.small=assignedSlots sources (Template.current (Template.initial m k) l) y)
    (hbulk : ∀u : Fin (2^l)×Fin m,
      bulkSamples sources m k l y u.1 u.2=bulkSamples sources m k l x (σ u).1 (σ u).2)
    {outside : List ℕ} (hs : old.Supported V outside) (hs' : old'.Supported V outside)
    (hmass : (assignmentPrior sources (Template.current (Template.initial m k) l)).mass x≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j))
    (z : ZMod ((pairedFrequencyProduct old old')^(K+2)) ×
      ZMod ((pairedFrequencyProduct old old')^(K+2))) :
    independentRTest K old old' σ z
      (sourceBulkUnits ((pairedFrequencyProduct old old')^(K+2)) sources m k l x)=
    independentReferenceIndicator K old old'
      (decodeHistory sources (Template.initial m k) V l a c)
      (decodeHistory sources (Template.initial m k) V l a' c') z := by
  let M := (pairedFrequencyProduct old old')^(K+2)
  have hcop := source_bulk_coprime_frequency_power old old' hs hs' hfreq
    (Template.current (Template.initial m k) l) x hmass (K+2)
  have hsample := sourceBulkUnits_coe M sources m k l x hcop
  have hleft := frequencyLeaves_decode_slots M sources m k V l a c x hx
    (sourceBulkUnits M sources m k l x) hsample
  have hright := frequencyLeaves_decode_slots_related M m k l sources V a' c' x y σ hy hbulk
    (sourceBulkUnits M sources m k l x) hsample
  unfold independentRTest independentReferenceIndicator
  dsimp only
  rw [hleft,hright]

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequency

end

end OAI
