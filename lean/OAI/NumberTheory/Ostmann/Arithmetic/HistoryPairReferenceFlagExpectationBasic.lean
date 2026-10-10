import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagsTransport

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction Construction.CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairFlags
open HistoryPairRepresentativeVariables HistoryPairReferenceFlagsTransport
open PolynomialFlagReplacementFinite

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}

def family (D E : DecodedDraw sources seed V outside l)
    (x : PairKey D.history E.history → ℤ) : ℝ :=
  ∑ r : Representative D.history E.history, ∑ j : Index D.history E.history r,
    flagError (polynomial D.history E.history D.supported E.supported r j) x
      (x (representativeMap D.history E.history r)).toNat

def pullSample (D E D0 E0 : DecodedDraw sources seed V outside l)
    (hp : SamePairPattern seed D.history E.history D0.history E0.history
      D.labels E.labels D0.labels E0.labels)
    (x : PairKey D.history E.history → ℤ) : PairKey D0.history E0.history → ℤ :=
  x ∘ (pairedBlockEquiv D E D0 E0 hp).symm

@[simp] theorem pullSample_apply (D E D0 E0 : DecodedDraw sources seed V outside l)
    (hp : SamePairPattern seed D.history E.history D0.history E0.history
      D.labels E.labels D0.labels E0.labels)
    (x : PairKey D.history E.history → ℤ) (i : PairKey D.history E.history) :
    pullSample D E D0 E0 hp x (pairedBlockEquiv D E D0 E0 hp i)=x i := by
  simp only [pullSample,Function.comp_apply,Equiv.symm_apply_apply]

@[simp] theorem pullSample_comp (D E D0 E0 : DecodedDraw sources seed V outside l)
    (hp : SamePairPattern seed D.history E.history D0.history E0.history
      D.labels E.labels D0.labels E0.labels)
    (x : PairKey D.history E.history → ℤ) :
    pullSample D E D0 E0 hp x ∘ pairedBlockEquiv D E D0 E0 hp=x := by
  funext i
  exact pullSample_apply D E D0 E0 hp x i

theorem family_nonneg (D E : DecodedDraw sources seed V outside l)
    (x : PairKey D.history E.history → ℤ) : 0 ≤ family D E x := by
  exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun j _ => flagError_nonneg _ _ _))

theorem family_eq_pullSample (D E D0 E0 : DecodedDraw sources seed V outside l)
    (hD : D.SameFrequencies D0) (hE : E.SameFrequencies E0)
    (hp : SamePairPattern seed D.history E.history D0.history E0.history
      D.labels E.labels D0.labels E0.labels)
    (x : PairKey D.history E.history → ℤ) :
    family D E x=family D0 E0 (pullSample D E D0 E0 hp x) := by
  have he := sum_sum_flagError_eq D E D0 E0 hD hE hp
    (pullSample D E D0 E0 hp x)
    (fun r => (pullSample D E D0 E0 hp x (representativeMap D0.history E0.history r)).toNat)
  simpa only [family,pullSample_comp,representativeEquiv_variable,pullSample_apply] using he

theorem actual_family_eq_fixed (D E D0 E0 : DecodedDraw sources seed V outside l)
    (hD : D.SameFrequencies D0) (hE : E.SameFrequencies E0)
    (hp : SamePairPattern seed D.history E.history D0.history E0.history
      D.labels E.labels D0.labels E0.labels) :
    family D E (pairSample D.history E.history)=
      family D0 E0 (pullSample D E D0 E0 hp (pairSample D.history E.history)) :=
  family_eq_pullSample D E D0 E0 hD hE hp _

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
