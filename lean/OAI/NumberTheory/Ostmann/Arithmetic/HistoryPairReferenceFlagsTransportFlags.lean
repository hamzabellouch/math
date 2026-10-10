import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagsTransportBasic
import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialFlagReplacementFiniteReindex

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

theorem flags_rename (i : Occurrences D.history E.history) :
    rename (pairedBlockEquiv D E D' E' hp)
      (leftFlag D.history E.history D.supported E.supported i)=
      leftFlag D'.history E'.history D'.supported E'.supported (occurrenceEquiv D E D' E' i) ∧
    rename (pairedBlockEquiv D E D' E' hp)
      (rightFlag D.history E.history D.supported E.supported i)=
      rightFlag D'.history E'.history D'.supported E'.supported (occurrenceEquiv D E D' E' i) := by
  obtain ⟨i,rfl⟩ := (pairedOccurrenceEquiv D E).surjective i
  rw [occurrenceEquiv_apply]
  exact decoded_pair_flags_rename D E D' E' hD hE hp i

theorem minor_rename (i j : Occurrences D.history E.history) :
    rename (pairedBlockEquiv D E D' E' hp)
      (minorFlag D.history E.history D.supported E.supported i j)=
      minorFlag D'.history E'.history D'.supported E'.supported
        (occurrenceEquiv D E D' E' i) (occurrenceEquiv D E D' E' j) := by
  obtain ⟨i,rfl⟩ := (pairedOccurrenceEquiv D E).surjective i
  obtain ⟨j,rfl⟩ := (pairedOccurrenceEquiv D E).surjective j
  rw [occurrenceEquiv_apply,occurrenceEquiv_apply]
  exact decoded_pair_minor_rename D E D' E' hD hE hp i j

theorem polynomial_rename (r : Representative D.history E.history) (j : Index D.history E.history r) :
    rename (pairedBlockEquiv D E D' E' hp)
      (polynomial D.history E.history D.supported E.supported r j)=
      polynomial D'.history E'.history D'.supported E'.supported
        (representativeEquiv D E D' E' hp r) (indexEquiv D E D' E' hp r j) := by
  rcases j with ⟨i,b⟩ | ⟨i,j⟩
  · cases b
    · exact (flags_rename D E D' E' hD hE hp i.val).1
    · exact (flags_rename D E D' E' hD hE hp i.val).2
  · exact minor_rename D E D' E' hD hE hp i.val j.val

theorem polynomial_zero_iff (r : Representative D.history E.history) (j : Index D.history E.history r) :
    polynomial D.history E.history D.supported E.supported r j=0 ↔
      polynomial D'.history E'.history D'.supported E'.supported
        (representativeEquiv D E D' E' hp r) (indexEquiv D E D' E' hp r j)=0 := by
  rw [← polynomial_rename D E D' E' hD hE hp r j]
  exact (rename_eq_zero_iff_of_injective _ (pairedBlockEquiv D E D' E' hp).injective).symm

theorem polynomial_totalDegree (r : Representative D.history E.history) (j : Index D.history E.history r) :
    (polynomial D'.history E'.history D'.supported E'.supported
      (representativeEquiv D E D' E' hp r) (indexEquiv D E D' E' hp r j)).totalDegree=
      (polynomial D.history E.history D.supported E.supported r j).totalDegree := by
  rw [← polynomial_rename D E D' E' hD hE hp r j,totalDegree_rename_equiv]

theorem polynomial_eval {A : Type*} [CommRing A]
    (r : Representative D.history E.history) (j : Index D.history E.history r)
    (x : PairKey D'.history E'.history → A) :
    eval₂ (Int.castRingHom A) x
      (polynomial D'.history E'.history D'.supported E'.supported
        (representativeEquiv D E D' E' hp r) (indexEquiv D E D' E' hp r j))=
    eval₂ (Int.castRingHom A) (x ∘ pairedBlockEquiv D E D' E' hp)
      (polynomial D.history E.history D.supported E.supported r j) := by
  rw [← polynomial_rename D E D' E' hD hE hp r j,eval₂_rename]

theorem flagError_eq (r : Representative D.history E.history) (j : Index D.history E.history r)
    (x : PairKey D'.history E'.history → ℤ) (b : ℕ) :
    flagError (polynomial D'.history E'.history D'.supported E'.supported
      (representativeEquiv D E D' E' hp r) (indexEquiv D E D' E' hp r j)) x b=
    flagError (polynomial D.history E.history D.supported E.supported r j)
      (x ∘ pairedBlockEquiv D E D' E' hp) b := by
  rw [← polynomial_rename D E D' E' hD hE hp r j,flagError_rename_equiv]

theorem sum_flagError_eq (r : Representative D.history E.history)
    (x : PairKey D'.history E'.history → ℤ) (b : ℕ) :
    (∑ j : Index D.history E.history r,
      flagError (polynomial D.history E.history D.supported E.supported r j)
        (x ∘ pairedBlockEquiv D E D' E' hp) b)=
    ∑ j : Index D'.history E'.history (representativeEquiv D E D' E' hp r),
      flagError (polynomial D'.history E'.history D'.supported E'.supported
        (representativeEquiv D E D' E' hp r) j) x b := by
  calc
    _ = ∑ j : Index D.history E.history r,
        flagError (polynomial D'.history E'.history D'.supported E'.supported
          (representativeEquiv D E D' E' hp r) (indexEquiv D E D' E' hp r j)) x b := by
      apply Finset.sum_congr rfl
      intro j _
      exact (flagError_eq D E D' E' hD hE hp r j x b).symm
    _ = _ := (indexEquiv D E D' E' hp r).sum_comp (fun j =>
      flagError (polynomial D'.history E'.history D'.supported E'.supported
        (representativeEquiv D E D' E' hp r) j) x b)

end Ostmann.Arithmetic.HistoryPairReferenceFlagsTransport

end

end OAI
