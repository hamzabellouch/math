import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkDiagramParametersBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealizationMetadata

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFrequencyTransport
open Construction HistoryBulkProducts HistoryBulkDiagramParameters HistoryFrequencyResidues

def SameFrequencyData : {l : ℕ} → History l → History l → Prop
  | _, .leaf a, .leaf b => a.frequency=b.frequency
  | _, .node a _ u hp hm left right, .node b _ u' hp' hm' left' right' =>
    a.frequency=b.frequency ∧ fixedProduct hp=fixedProduct hp' ∧
    fixedProduct hm=fixedProduct hm' ∧ (u.map SmallSlot.value).prod=(u'.map SmallSlot.value).prod ∧
    SameFrequencyData left left' ∧ SameFrequencyData right right'

theorem SameFrequencyData.root_frequency_eq {l : ℕ} {h g : History l}
    (hfg : SameFrequencyData h g) : h.root.frequency=g.root.frequency := by
  cases h <;> cases g
  · exact hfg
  · exact hfg.1

theorem SameFrequencyData.frequencies_eq {l : ℕ} {h g : History l}
    (hfg : SameFrequencyData h g) : h.frequencies=g.frequencies := by
  induction h with
  | leaf a => cases g with | leaf b => simpa [History.frequencies,SameFrequencyData] using hfg
  | node a p u hp hm left right il ir =>
    cases g with
    | node b p' u' hp' hm' left' right' =>
      simp only [History.frequencies, hfg.1, il hfg.2.2.2.2.1, ir hfg.2.2.2.2.2]

theorem sameFrequencyData_decode (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (hf : a.frequency=b.frequency)
    (hab : a.small.map eraseBulkValue=b.small.map eraseBulkValue) :
    SameFrequencyData (decodeHistory sources seed V l a c)
      (decodeHistory sources seed V l b c) := by
  induction l generalizing a b with
  | zero => exact hf
  | succ l ih =>
    let T := Template.current seed l
    let n := (Template.remainder (l+1) T).length
    let u := assignedSlots sources (Template.extracted (l+1) T) c.2.2.1
    simp only [decodeHistory, SameFrequencyData]
    refine ⟨hf, fixedProduct_eq_of_erase_eq (erase_take_eq hab n),
      fixedProduct_eq_of_erase_eq (erase_drop_eq hab n), by trivial, ?_, ?_⟩
    · exact ih _ _ _ rfl (erase_reinsert_eq (l+1) T u (erase_take_eq hab n))
    · exact ih _ _ _ rfl (erase_reinsert_eq (l+1) T u (erase_drop_eq hab n))

theorem pairedFrequencyProduct_eq {l : ℕ} {h g h' g' : History l}
    (ha : SameFrequencyData h g) (hb : SameFrequencyData h' g') :
    pairedFrequencyProduct h h'=pairedFrequencyProduct g g' := by
  simp only [pairedFrequencyProduct, ha.frequencies_eq, hb.frequencies_eq]

end Ostmann.Arithmetic.HistoryBulkFrequencyTransport

end

end OAI
