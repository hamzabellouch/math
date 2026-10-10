import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkDiagramParametersBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramEvaluation

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkDiagramParameters
open Construction HistoryBulkProducts HistoryResidueRegular HistoryTreeParameters
  HistorySignedSpectatorDiagram
variable {q : ℕ} [Fact q.Prime]

theorem parameters_decode_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c : HistoryChoices sources seed V l)
    (hf : a.frequency=b.frequency)
    (hab : a.small.map eraseBulkValue=b.small.map eraseBulkValue)
    (ha : (decodeHistory sources seed V l a c).Supported V outside)
    (hb : (decodeHistory sources seed V l b c).Supported V outside)
    (hra : Regular q (decodeHistory sources seed V l a c))
    (hrb : Regular q (decodeHistory sources seed V l b c)) (sign : Bool) :
    parameters V outside (decodeHistory sources seed V l a c) ha hra sign=
      parameters V outside (decodeHistory sources seed V l b c) hb hrb sign := by
  induction l generalizing a b sign with
  | zero =>
    apply congrArg (fun u => Tree.Parameters.leaf u sign)
    apply Units.ext
    change (a.frequency:ZMod q)=(b.frequency:ZMod q)
    rw [hf]
  | succ l ih =>
    let T := Template.current seed l
    let n := (Template.remainder (l+1) T).length
    let u := assignedSlots sources (Template.extracted (l+1) T) c.2.2.1
    simp only [decodeHistory,parameters]
    congr 1
    · apply Units.ext
      change (a.frequency:ZMod q)=(b.frequency:ZMod q)
      rw [hf]
    · apply Units.ext
      change (fixedProduct (a.small.take n):ZMod q)=(fixedProduct (b.small.take n):ZMod q)
      rw [fixedProduct_eq_of_erase_eq (erase_take_eq hab n)]
    · apply Units.ext
      change (fixedProduct (a.small.drop n):ZMod q)=(fixedProduct (b.small.drop n):ZMod q)
      rw [fixedProduct_eq_of_erase_eq (erase_drop_eq hab n)]
    · apply ih
      · rfl
      · exact erase_reinsert_eq (l+1) T u (erase_take_eq hab n)
    · apply ih
      · rfl
      · exact erase_reinsert_eq (l+1) T u (erase_drop_eq hab n)

theorem variableDiagram_decode_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c : HistoryChoices sources seed V (l+1))
    (hf : a.frequency=b.frequency)
    (hab : a.small.map eraseBulkValue=b.small.map eraseBulkValue)
    (ha : (decodeHistory sources seed V (l+1) a c).Supported V outside)
    (hb : (decodeHistory sources seed V (l+1) b c).Supported V outside)
    (hra : Regular q (decodeHistory sources seed V (l+1) a c))
    (hrb : Regular q (decodeHistory sources seed V (l+1) b c))
    (D Xp Xm : (ZMod q)ˣ) :
    variableDiagram (decodeHistory sources seed V (l+1) a c) ha hra D Xp Xm=
      variableDiagram (decodeHistory sources seed V (l+1) b c) hb hrb D Xp Xm := by
  have hp := parameters_decode_eq sources seed V outside (l+1) a b c hf hab ha hb hra hrb false
  unfold variableDiagram
  congr 1

end Ostmann.Arithmetic.HistoryBulkDiagramParameters

end

end OAI
