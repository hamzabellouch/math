import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsFrequency
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealizationUnitsPair

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceTestsFrequency
open Construction Conclusion Characters HistoryBulkProducts HistoryFrequencyResidues
open HistoryPairedFrequencyAverage HistoryPairedFrequencyAverageHaar
open HistoryBulkSpectatorReferenceRaw CanonicalHistoryLeafBulk
open HistoryBulkResidueNormSum HistoryBulkSupportConverse

theorem source_bulk_coprime_frequency_power
    {sources : SourceFamily} {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (old old' : History l) (hs : old.Supported V outside)
    (hs' : old'.Supported V outside)
    (hfreq : ∀j ≤ l,∀origin,(sources origin).AboveFrequency (V j))
    (T : List SourceSlot) (x : SourceAssignment sources T)
    (hmass : (assignmentPrior sources T).mass x ≠ 0) (n : ℕ) :
    Nat.Coprime (bulkProduct (assignedSlots sources T x))
      ((pairedFrequencyProduct old old')^n) := by
  apply source_bulkProduct_coprime sources _
    (fun q hq => sourceMass_coprime_paired_frequency old old' hs hs' hfreq q hq n)
  exact assignedSlots_source_mass_ne_zero sources T x hmass

theorem independentRTest_source_eq_reference_of_mass
    (K b k l : ℕ) (bulk : PrimeSource) (top : Fin 3 → PrimeSource)
    (comp : Fin k → Fin 2 → PrimeSource) (V : ℕ → ℕ)
    (old old' : History l) (a a' : State)
    (c c' : HistoryChoices (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l))
    (hx : a.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l) x)
    (hx' : a'.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l)
      (leafBulkAssignmentPermutation b k l bulk top comp σ x))
    {outside : List ℕ} (hs : old.Supported V outside)
    (hs' : old'.Supported V outside)
    (hmass : (assignmentPrior (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l)).mass x ≠ 0)
    (hfreq : ∀j ≤ l,∀origin,
      ((initialSourceFamily b k bulk top comp) origin).AboveFrequency (V j))
    (z : ZMod ((pairedFrequencyProduct old old')^(K+2)) ×
      ZMod ((pairedFrequencyProduct old old')^(K+2))) :
    independentRTest K old old' σ z
      (sourceBulkUnits ((pairedFrequencyProduct old old')^(K+2))
        (initialSourceFamily b k bulk top comp) (2*b) k l x) =
      independentReferenceIndicator K old old'
        (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a c)
        (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a' c') z := by
  have hc := source_bulk_coprime_frequency_power old old' hs hs' hfreq
    (Template.current (Template.initial (2*b) k) l) x hmass (K+2)
  rw [←hx] at hc
  exact independentRTest_source_eq_reference K b k l bulk top comp V old old' a a'
    c c' σ x hx hx' hc z

theorem canonicalRTest_source_eq_reference_of_mass
    (K m k l : ℕ) (sources : SourceFamily) (V : ℕ → ℕ)
    (old old' : History l) (a : State)
    (c : HistoryChoices sources (Template.initial m k) V l)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hx : a.small=assignedSlots sources (Template.current (Template.initial m k) l) x)
    {outside : List ℕ} (hs : old.Supported V outside)
    (hs' : old'.Supported V outside)
    (hmass : (assignmentPrior sources
      (Template.current (Template.initial m k) l)).mass x ≠ 0)
    (hfreq : ∀j ≤ l,∀origin,(sources origin).AboveFrequency (V j))
    (z : ZMod ((pairedFrequencyProduct old old')^(K+2)) ×
      ZMod ((pairedFrequencyProduct old old')^(K+2))) :
    canonicalRTest K old old' z
      (sourceBulkUnits ((pairedFrequencyProduct old old')^(K+2)) sources m k l x) =
      leafIndicator K (pairedFrequencyProduct old old') (frequencySchedule old old')
        (fixedFactorSchedule old old') old old' []
        (l,initialResidueGiants K (pairedFrequencyProduct old old') z,
          initialResidueGiants K (pairedFrequencyProduct old old') z)
        (frequencyLeaves ((pairedFrequencyProduct old old')^(K+2))
          (decodeHistory sources (Template.initial m k) V l a c)) := by
  have hc := source_bulk_coprime_frequency_power old old' hs hs' hfreq
    (Template.current (Template.initial m k) l) x hmass (K+2)
  rw [←hx] at hc
  exact canonicalRTest_source_eq_reference K m k l sources V old old' a c x hx hc z

end Ostmann.Arithmetic.HistoryBulkReferenceTestsFrequency

end

end OAI
