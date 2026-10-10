import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFrequencyTransportIndicator

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFrequencyTransport
open Construction HistoryBulkDiagramParameters HistoryFrequencyResidues
open HistorySignedResidueFactorization HistoryPairedFrequencyAverage

theorem pairedIndicator_decode_eq_reference (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a b a' b' : State)
    (c c' : HistoryChoices sources seed V l)
    (hf : a.frequency=b.frequency) (hf' : a'.frequency=b'.frequency)
    (hab : a.small.map eraseBulkValue=b.small.map eraseBulkValue)
    (hab' : a'.small.map eraseBulkValue=b'.small.map eraseBulkValue) (K : ℕ) :
    let h := decodeHistory sources seed V l a c
    let g := decodeHistory sources seed V l b c
    let h' := decodeHistory sources seed V l a' c'
    let g' := decodeHistory sources seed V l b' c'
    ∃ hR : pairedFrequencyProduct h h'=pairedFrequencyProduct g g',
      ∀ z : ZMod ((pairedFrequencyProduct g g')^(K+2)) ×
        ZMod ((pairedFrequencyProduct g g')^(K+2)),
      pairedFrequencyResidueIndicator K h h' (residuePairTransport K hR z)=
        leafIndicator K (pairedFrequencyProduct g g') (frequencySchedule g g')
          (fixedFactorSchedule g g') g g' []
          (l,initialResidueGiants K (pairedFrequencyProduct g g') z,
            initialResidueGiants K (pairedFrequencyProduct g g') z)
          (frequencyLeaves ((pairedFrequencyProduct g g')^(K+2)) h) := by
  dsimp only
  have ha := sameFrequencyData_decode sources seed V l a b c hf hab
  have hb := sameFrequencyData_decode sources seed V l a' b' c' hf' hab'
  refine ⟨pairedFrequencyProduct_eq ha hb, ?_⟩
  intro z
  exact pairedIndicator_eq_reference ha hb K z

theorem pairedIndicator_assigned_eq_reference (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
    (x y : SourceAssignment sources (Template.current seed l))
    (hxy : ∀i : Fin (Template.current seed l).length,
      (Template.current seed l)[i].role≠.bulk → (x i : ℕ)=(y i : ℕ))
    (s t : ℤ) (Gp Gm Gp' Gm' : ℕ) (c c' : HistoryChoices sources seed V l) (K : ℕ) :
    let a : State := ⟨s,Gp,Gm,assignedSlots sources (Template.current seed l) x⟩
    let b : State := ⟨s,Gp',Gm',assignedSlots sources (Template.current seed l) y⟩
    let a' : State := ⟨t,Gp,Gm,assignedSlots sources (Template.current seed l) x⟩
    let b' : State := ⟨t,Gp',Gm',assignedSlots sources (Template.current seed l) y⟩
    let h := decodeHistory sources seed V l a c
    let g := decodeHistory sources seed V l b c
    let h' := decodeHistory sources seed V l a' c'
    let g' := decodeHistory sources seed V l b' c'
    ∃ hR : pairedFrequencyProduct h h'=pairedFrequencyProduct g g',
      ∀ z : ZMod ((pairedFrequencyProduct g g')^(K+2)) ×
        ZMod ((pairedFrequencyProduct g g')^(K+2)),
      pairedFrequencyResidueIndicator K h h' (residuePairTransport K hR z)=
        leafIndicator K (pairedFrequencyProduct g g') (frequencySchedule g g')
          (fixedFactorSchedule g g') g g' []
          (l,initialResidueGiants K (pairedFrequencyProduct g g') z,
            initialResidueGiants K (pairedFrequencyProduct g g') z)
          (frequencyLeaves ((pairedFrequencyProduct g g')^(K+2)) h) := by
  dsimp only
  exact pairedIndicator_decode_eq_reference sources seed V l
    ⟨s,Gp,Gm,assignedSlots sources (Template.current seed l) x⟩
    ⟨s,Gp',Gm',assignedSlots sources (Template.current seed l) y⟩
    ⟨t,Gp,Gm,assignedSlots sources (Template.current seed l) x⟩
    ⟨t,Gp',Gm',assignedSlots sources (Template.current seed l) y⟩ c c' rfl rfl
    (assignedSlots_erase_eq sources (Template.current seed l) x y hxy)
    (assignedSlots_erase_eq sources (Template.current seed l) x y hxy) K

end Ostmann.Arithmetic.HistoryBulkFrequencyTransport

end

end OAI
