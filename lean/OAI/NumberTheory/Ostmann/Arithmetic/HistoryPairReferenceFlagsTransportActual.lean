import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportDecoded
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagsTransportFamilies

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagsTransport
open scoped BigOperators
open Construction Construction.CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairFlags
open HistoryPairBulkTransport MvPolynomial PolynomialFlagReplacementFinite

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}
variable (D E D' E' : DecodedDraw sources seed V outside l)
  (σ : Equiv.Perm (Fin (Template.current seed l).length))
  (hroot : ∀ i, coordinateSample seed E.history E.labels (.inr (.inl i))=
    coordinateSample seed D.history D.labels (.inr (.inl (σ i))))
  (hroot' : ∀ i, coordinateSample seed E'.history E'.labels (.inr (.inl i))=
    coordinateSample seed D'.history D'.labels (.inr (.inl (σ i))))
  (hpattern : pairedDrawPattern sources seed V l D.choices E.choices=
    pairedDrawPattern sources seed V l D'.choices E'.choices)

include σ hroot hroot' hpattern in

theorem samePairPattern_of_drawPattern :
    SamePairPattern seed D.history E.history D'.history E'.history
      D.labels E.labels D'.labels E'.labels :=
  samePairPattern_decoded sources seed V outside l D.root E.root D'.root E'.root
    D.choices E.choices D'.choices E'.choices D.sourceMatch E.sourceMatch D'.sourceMatch E'.sourceMatch
    D.supported D'.supported σ hroot hroot' hpattern

def drawBlockEquiv : PairKey D.history E.history ≃ PairKey D'.history E'.history :=
  pairedBlockEquiv D E D' E' (samePairPattern_of_drawPattern D E D' E' σ hroot hroot' hpattern)

def drawRepresentativeEquiv : Representative D.history E.history ≃ Representative D'.history E'.history :=
  representativeEquiv D E D' E' (samePairPattern_of_drawPattern D E D' E' σ hroot hroot' hpattern)

def drawIndexEquiv (r : Representative D.history E.history) :
    Index D.history E.history r ≃
      Index D'.history E'.history (drawRepresentativeEquiv D E D' E' σ hroot hroot' hpattern r) :=
  indexEquiv D E D' E' (samePairPattern_of_drawPattern D E D' E' σ hroot hroot' hpattern) r

theorem drawPattern_polynomial_rename (hD : D.SameFrequencies D') (hE : E.SameFrequencies E')
    (r : Representative D.history E.history) (j : Index D.history E.history r) :
    rename (drawBlockEquiv D E D' E' σ hroot hroot' hpattern)
      (polynomial D.history E.history D.supported E.supported r j)=
      polynomial D'.history E'.history D'.supported E'.supported
        (drawRepresentativeEquiv D E D' E' σ hroot hroot' hpattern r)
        (drawIndexEquiv D E D' E' σ hroot hroot' hpattern r j) :=
  polynomial_rename D E D' E' hD hE
    (samePairPattern_of_drawPattern D E D' E' σ hroot hroot' hpattern) r j

theorem drawPattern_symbolicKernel_eq (hD : D.SameFrequencies D') (hE : E.SameFrequencies E')
    (mixed : Bool) (r : Representative D.history E.history) (b : ℕ) :
    HistoryPairKernelReplacement.symbolicKernel mixed D.history E.history D.supported E.supported r b=
    HistoryPairKernelReplacement.symbolicKernel mixed D'.history E'.history D'.supported E'.supported
      (drawRepresentativeEquiv D E D' E' σ hroot hroot' hpattern r) b :=
  symbolicKernel_eq D E D' E' hD hE
    (samePairPattern_of_drawPattern D E D' E' σ hroot hroot' hpattern) mixed r b

theorem drawPattern_sum_flagError_eq (hD : D.SameFrequencies D') (hE : E.SameFrequencies E')
    (r : Representative D.history E.history) (x : PairKey D'.history E'.history → ℤ) (b : ℕ) :
    (∑ j : Index D.history E.history r,
      flagError (polynomial D.history E.history D.supported E.supported r j)
        (x ∘ drawBlockEquiv D E D' E' σ hroot hroot' hpattern) b)=
    ∑ j : Index D'.history E'.history (drawRepresentativeEquiv D E D' E' σ hroot hroot' hpattern r),
      flagError (polynomial D'.history E'.history D'.supported E'.supported
        (drawRepresentativeEquiv D E D' E' σ hroot hroot' hpattern r) j) x b :=
  sum_flagError_eq D E D' E' hD hE
    (samePairPattern_of_drawPattern D E D' E' σ hroot hroot' hpattern) r x b

end Ostmann.Arithmetic.HistoryPairReferenceFlagsTransport

end

end OAI
