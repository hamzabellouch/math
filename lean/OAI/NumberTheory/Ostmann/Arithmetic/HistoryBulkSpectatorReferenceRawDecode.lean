import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawEvaluation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSkeletonDecode

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw
open Construction HistoryBulkProducts HistoryBulkSupportConverse HistoryBulkFrequencyTransport
open HistoryBulkDiagramParameters HistoryResidueRegular HistorySignedSpectatorDiagram
open HistoryBulkSpectatorDiagramAverage
variable {q : ℕ} [Fact q.Prime]

theorem bulkDiagram_decode_value_raw (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (hf : a.frequency=b.frequency)
    (hab : a.small.map eraseBulkValue=b.small.map eraseBulkValue)
    (hbprime : b.PrimeSmall) (hc : Nat.Coprime (bulkProduct b.small) q)
    (hq : q∈outside) (hV : ∀j≤l,V j<q)
    (D Xp Xm : (ZMod q)ˣ) (g : ZMod q→ℂ) (hg : g 0=0) :
    (bulkDiagram (decodeHistory sources seed V l a c) hs
      (supported_regular _ hs hq hV) D Xp Xm).value g
        (rawLeaves q (decodeHistory sources seed V l b c))=
      primeSpectator q g D (decodeHistory sources seed V l b c) Xp Xm :=
  bulkDiagram_value_raw _ _ hs (supported_regular _ hs hq hV)
    (staticSkeleton_decode_redraw sources seed V l a b c ha hb hs hf hbprime)
    (sameFrequencyData_decode sources seed V l a b c hf hab)
    (by simpa only [decodeHistory_root] using fixedProduct_eq_of_erase_eq hab)
    (by simpa only [decodeHistory_root] using hc) D Xp Xm g hg

end Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw

end

end OAI
