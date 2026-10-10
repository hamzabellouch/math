import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagsTransportKernels

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagsTransport
open scoped BigOperators
open Construction Construction.CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairFlags
open MvPolynomial PolynomialFlagReplacementFinite

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}
variable (D E D' E' : DecodedDraw sources seed V outside l)
  (hD : D.SameFrequencies D') (hE : E.SameFrequencies E')
  (hp : SamePairPattern seed D.history E.history D'.history E'.history
    D.labels E.labels D'.labels E'.labels)
include hD hE

theorem noAccidentalFlags_iff (r : Representative D.history E.history)
    (b : ℕ) (x : PairKey D'.history E'.history → ZMod b) :
    HistoryPairKernelReplacement.NoAccidentalFlags D.history E.history D.supported E.supported r b
      (x ∘ pairedBlockEquiv D E D' E' hp) ↔
    HistoryPairKernelReplacement.NoAccidentalFlags D'.history E'.history D'.supported E'.supported
      (representativeEquiv D E D' E' hp r) b x := by
  constructor
  · intro hh j
    obtain ⟨j,rfl⟩ := (indexEquiv D E D' E' hp r).surjective j
    rw [polynomial_eval D E D' E' hD hE hp r j,
      ← polynomial_zero_iff D E D' E' hD hE hp r j]
    exact hh j
  · intro hh j
    have hj := hh (indexEquiv D E D' E' hp r j)
    rw [polynomial_eval D E D' E' hD hE hp r j,
      ← polynomial_zero_iff D E D' E' hD hE hp r j] at hj
    exact hj

theorem sum_sum_flagError_eq (x : PairKey D'.history E'.history → ℤ)
    (b : Representative D'.history E'.history → ℕ) :
    (∑ r : Representative D.history E.history, ∑ j : Index D.history E.history r,
      flagError (polynomial D.history E.history D.supported E.supported r j)
        (x ∘ pairedBlockEquiv D E D' E' hp) (b (representativeEquiv D E D' E' hp r)))=
    ∑ r : Representative D'.history E'.history, ∑ j : Index D'.history E'.history r,
      flagError (polynomial D'.history E'.history D'.supported E'.supported r j) x (b r) := by
  simp_rw [sum_flagError_eq D E D' E' hD hE hp]
  exact (representativeEquiv D E D' E' hp).sum_comp (fun r =>
    ∑ j : Index D'.history E'.history r,
      flagError (polynomial D'.history E'.history D'.supported E'.supported r j) x (b r))

theorem sum_totalDegree_eq (r : Representative D.history E.history) :
    (∑ j : Index D.history E.history r,
      (polynomial D.history E.history D.supported E.supported r j).totalDegree)=
    ∑ j : Index D'.history E'.history (representativeEquiv D E D' E' hp r),
      (polynomial D'.history E'.history D'.supported E'.supported
        (representativeEquiv D E D' E' hp r) j).totalDegree := by
  calc
    _ = ∑ j : Index D.history E.history r,
        (polynomial D'.history E'.history D'.supported E'.supported
          (representativeEquiv D E D' E' hp r) (indexEquiv D E D' E' hp r j)).totalDegree := by
      apply Finset.sum_congr rfl
      intro j _
      exact (polynomial_totalDegree D E D' E' hD hE hp r j).symm
    _ = _ := (indexEquiv D E D' E' hp r).sum_comp (fun j =>
      (polynomial D'.history E'.history D'.supported E'.supported
        (representativeEquiv D E D' E' hp r) j).totalDegree)

end Ostmann.Arithmetic.HistoryPairReferenceFlagsTransport

end

end OAI
