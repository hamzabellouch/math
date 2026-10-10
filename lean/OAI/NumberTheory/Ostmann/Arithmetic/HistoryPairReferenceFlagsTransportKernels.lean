import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacementPointwise
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagsTransportFlags

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagsTransport
open scoped BigOperators
open Construction Construction.CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairFlags
open MvPolynomial PolynomialFlagReplacementFinite HistoryPairKernelReplacement

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}
variable (D E D' E' : DecodedDraw sources seed V outside l)
  (hD : D.SameFrequencies D') (hE : E.SameFrequencies E')
  (hp : SamePairPattern seed D.history E.history D'.history E'.history
    D.labels E.labels D'.labels E'.labels)
include hD hE

theorem leftFlag_zero_iff (r : Representative D.history E.history) (i : Fiber D.history E.history r) :
    leftFlag D.history E.history D.supported E.supported i.val=0 ↔
      leftFlag D'.history E'.history D'.supported E'.supported (fiberEquiv D E D' E' hp r i).val=0 :=
  polynomial_zero_iff D E D' E' hD hE hp r (.inl (i,false))

theorem rightFlag_zero_iff (r : Representative D.history E.history) (i : Fiber D.history E.history r) :
    rightFlag D.history E.history D.supported E.supported i.val=0 ↔
      rightFlag D'.history E'.history D'.supported E'.supported (fiberEquiv D E D' E' hp r i).val=0 :=
  polynomial_zero_iff D E D' E' hD hE hp r (.inl (i,true))

theorem minorFlag_zero_iff (r : Representative D.history E.history) (i j : Fiber D.history E.history r) :
    minorFlag D.history E.history D.supported E.supported i.val j.val=0 ↔
      minorFlag D'.history E'.history D'.supported E'.supported
        (fiberEquiv D E D' E' hp r i).val (fiberEquiv D E D' E' hp r j).val=0 :=
  polynomial_zero_iff D E D' E' hD hE hp r (.inr (i,j))

theorem all_minors_zero_iff (r : Representative D.history E.history) :
    (∀ i j : Fiber D.history E.history r, minorFlag D.history E.history D.supported E.supported i.val j.val=0) ↔
    ∀ i j : Fiber D'.history E'.history (representativeEquiv D E D' E' hp r),
      minorFlag D'.history E'.history D'.supported E'.supported i.val j.val=0 := by
  constructor
  · intro hh i j
    obtain ⟨i,rfl⟩ := (fiberEquiv D E D' E' hp r).surjective i
    obtain ⟨j,rfl⟩ := (fiberEquiv D E D' E' hp r).surjective j
    exact (minorFlag_zero_iff D E D' E' hD hE hp r i j).mp (hh i j)
  · intro hh i j
    exact (minorFlag_zero_iff D E D' E' hD hE hp r i j).mpr (hh _ _)

theorem exists_two_nonzero_iff (r : Representative D.history E.history) :
    (∃ i : Fiber D.history E.history r,
      leftFlag D.history E.history D.supported E.supported i.val≠0 ∧
      rightFlag D.history E.history D.supported E.supported i.val≠0) ↔
    ∃ i : Fiber D'.history E'.history (representativeEquiv D E D' E' hp r),
      leftFlag D'.history E'.history D'.supported E'.supported i.val≠0 ∧
      rightFlag D'.history E'.history D'.supported E'.supported i.val≠0 := by
  constructor
  · rintro ⟨i,hl,hr⟩
    exact ⟨fiberEquiv D E D' E' hp r i,
      (not_congr (leftFlag_zero_iff D E D' E' hD hE hp r i)).mp hl,
      (not_congr (rightFlag_zero_iff D E D' E' hD hE hp r i)).mp hr⟩
  · rintro ⟨i,hl,hr⟩
    obtain ⟨i,rfl⟩ := (fiberEquiv D E D' E' hp r).surjective i
    exact ⟨i,(not_congr (leftFlag_zero_iff D E D' E' hD hE hp r i)).mpr hl,
      (not_congr (rightFlag_zero_iff D E D' E' hD hE hp r i)).mpr hr⟩

theorem exists_left_nonzero_iff (r : Representative D.history E.history) :
    (∃ i : Fiber D.history E.history r,
      leftFlag D.history E.history D.supported E.supported i.val≠0) ↔
    ∃ i : Fiber D'.history E'.history (representativeEquiv D E D' E' hp r),
      leftFlag D'.history E'.history D'.supported E'.supported i.val≠0 := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨fiberEquiv D E D' E' hp r i,
      (not_congr (leftFlag_zero_iff D E D' E' hD hE hp r i)).mp hi⟩
  · rintro ⟨i,hi⟩
    obtain ⟨i,rfl⟩ := (fiberEquiv D E D' E' hp r).surjective i
    exact ⟨i,(not_congr (leftFlag_zero_iff D E D' E' hD hE hp r i)).mpr hi⟩

theorem unitKernel_eq (r : Representative D.history E.history) (b : ℕ) :
    unitKernel D.history E.history D.supported E.supported r b=
      unitKernel D'.history E'.history D'.supported E'.supported (representativeEquiv D E D' E' hp r) b := by
  simp only [unitKernel,all_minors_zero_iff D E D' E' hD hE hp r,
    exists_two_nonzero_iff D E D' E' hD hE hp r]

theorem mixedKernel_eq (r : Representative D.history E.history) (b : ℕ) :
    mixedKernel D.history E.history D.supported E.supported r b=
      mixedKernel D'.history E'.history D'.supported E'.supported (representativeEquiv D E D' E' hp r) b := by
  simp only [mixedKernel,all_minors_zero_iff D E D' E' hD hE hp r,
    exists_left_nonzero_iff D E D' E' hD hE hp r]

theorem symbolicKernel_eq (mixed : Bool) (r : Representative D.history E.history) (b : ℕ) :
    symbolicKernel mixed D.history E.history D.supported E.supported r b=
      symbolicKernel mixed D'.history E'.history D'.supported E'.supported (representativeEquiv D E D' E' hp r) b := by
  simp only [symbolicKernel,unitKernel_eq D E D' E' hD hE hp r b,
    mixedKernel_eq D E D' E' hD hE hp r b]

theorem prod_symbolicKernel_eq (mixed : Bool) (b : Representative D'.history E'.history → ℕ) :
    (∏ r : Representative D.history E.history,
      symbolicKernel mixed D.history E.history D.supported E.supported r (b (representativeEquiv D E D' E' hp r)))=
    ∏ r : Representative D'.history E'.history,
      symbolicKernel mixed D'.history E'.history D'.supported E'.supported r (b r) := by
  simp_rw [symbolicKernel_eq D E D' E' hD hE hp]
  exact (representativeEquiv D E D' E' hp).prod_comp
    (fun r => symbolicKernel mixed D'.history E'.history D'.supported E'.supported r (b r))

end Ostmann.Arithmetic.HistoryPairReferenceFlagsTransport

end

end OAI
