import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsFrequencyBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceTestsFrequency
open Construction Conclusion Characters HistoryBulkProducts HistoryFrequencyResidues
open HistoryPairedFrequencyAverage HistoryPairedFrequencyAverageHaar
open HistoryBulkSpectatorReferenceRaw CanonicalHistoryLeafBulk
open HistoryBulkResidueNormSum HistoryBulkSupportConverse

theorem independentRTest_source_eq_reference
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
    (hc : Nat.Coprime (bulkProduct a.small) ((pairedFrequencyProduct old old')^(K+2)))
    (z : ZMod ((pairedFrequencyProduct old old')^(K+2)) ×
      ZMod ((pairedFrequencyProduct old old')^(K+2))) :
    independentRTest K old old' σ z
      (sourceBulkUnits ((pairedFrequencyProduct old old')^(K+2))
        (initialSourceFamily b k bulk top comp) (2*b) k l x) =
      independentReferenceIndicator K old old'
        (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a c)
        (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a' c') z := by
  let M := (pairedFrequencyProduct old old')^(K+2)
  let sources := initialSourceFamily b k bulk top comp
  have hcx : Nat.Coprime (bulkProduct
      (assignedSlots sources (Template.current (Template.initial (2*b) k) l) x)) M := by
    rw [←hx]
    exact hc
  have hsamples := sourceBulkUnits_coe M sources (2*b) k l x hcx
  have hl := frequencyLeaves_decode_slots M sources (2*b) k V l a c x hx
    (sourceBulkUnits M sources (2*b) k l x) hsamples
  have hr := frequencyLeaves_decode_slots_permuted M b k bulk top comp V l a' c' σ x hx'
    (sourceBulkUnits M sources (2*b) k l x) hsamples
  unfold independentRTest independentReferenceIndicator
  dsimp only
  rw [hl,hr]

theorem canonicalRTest_source_eq_reference
    (K m k l : ℕ) (sources : SourceFamily) (V : ℕ → ℕ)
    (old old' : History l) (a : State)
    (c : HistoryChoices sources (Template.initial m k) V l)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hx : a.small=assignedSlots sources (Template.current (Template.initial m k) l) x)
    (hc : Nat.Coprime (bulkProduct a.small) ((pairedFrequencyProduct old old')^(K+2)))
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
  have hcx : Nat.Coprime (bulkProduct
      (assignedSlots sources (Template.current (Template.initial m k) l) x))
      ((pairedFrequencyProduct old old')^(K+2)) := by
    rw [←hx]
    exact hc
  have hl := frequencyLeaves_decode_slots ((pairedFrequencyProduct old old')^(K+2)) sources m k V l a c x hx
    (sourceBulkUnits ((pairedFrequencyProduct old old')^(K+2)) sources m k l x)
    (sourceBulkUnits_coe _ sources m k l x hcx)
  unfold canonicalRTest
  rw [hl]

end Ostmann.Arithmetic.HistoryBulkReferenceTestsFrequency

end

end OAI
