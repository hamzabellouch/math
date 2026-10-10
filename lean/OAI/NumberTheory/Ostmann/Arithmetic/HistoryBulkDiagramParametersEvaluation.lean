import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkDiagramParameters

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkDiagramParameters
open Construction HistoryResidueRegular HistoryTreeParameters
  HistorySignedSpectatorDiagram HistorySignedSpectatorCRT
variable {q : ℕ} [Fact q.Prime]

theorem primeSpectator_decode_eq_referenceDiagram (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c : HistoryChoices sources seed V (l+1))
    (hf : a.frequency=b.frequency)
    (hab : a.small.map eraseBulkValue=b.small.map eraseBulkValue)
    (ha : (decodeHistory sources seed V (l+1) a c).Supported V outside)
    (hb : (decodeHistory sources seed V (l+1) b c).Supported V outside)
    (hq : q∈outside) (hV : ∀j≤l+1,V j<q)
    (g : ZMod q→ℂ) (hg : g 0=0) (D Xp Xm : (ZMod q)ˣ) :
    primeSpectator q g D (decodeHistory sources seed V (l+1) b c) Xp Xm=
      (variableDiagram (decodeHistory sources seed V (l+1) a c) ha
        (supported_regular _ ha hq hV) D Xp Xm).value g
        (leafBulk (decodeHistory sources seed V (l+1) b c)
          (supported_regular _ hb hq hV)) := by
  rw [variableDiagram_decode_eq sources seed V outside l a b c hf hab ha hb
    (supported_regular _ ha hq hV) (supported_regular _ hb hq hV) D Xp Xm]
  exact (variableDiagram_value _ hb (supported_regular _ hb hq hV) g hg D Xp Xm).symm

end Ostmann.Arithmetic.HistoryBulkDiagramParameters

end

end OAI
