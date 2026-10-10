import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMatchedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexSquare

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkFibreOriginalReference
open HistoryBulkFibreGiantApproximationReference HistoryPairRepresentatives
open HistoryPairReferenceSourceTransport
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ}
  {σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))}
  {J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ}
  {α : Type} [Fintype α] {w : α→ℝ} {P Q : α→ℤ}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}

namespace MatchedSelectedOuter
variable (R : MatchedSelectedOuter C p o outside σ J w P Q i)
  (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
    |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hprime : ∀q∈outside,q.Prime)

open HistoryBulkPrincipalBSquareReference HistoryBulkPrincipalBSquareReplacement
open HistoryBulkActualPrincipalSourceReindex HistoryRepresentativeSourceSeparation
open HistoryBulkReferencePeriodicMeanSource CanonicalHistoryLeafBulk
variable (had : PairAdmissible (R.frame (l:=l) hcell hprime).left (R.frame (l:=l) hcell hprime).right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

variable (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j))
include hfreq

theorem rawBTerm_prime_eq_squareBTerm (u : SelectedBulkSample C l)
    (hu : (selectedBulkPrior C l).mass u≠0) :
    R.rawBTerm (l:=l) hcell hprime false false u=R.squareBTerm (l:=l) hcell hprime had hout hV false false u := by
  have hleft := fibreAssignment_nonbulk_fixed (l:=l) C (outerNonbulk C l p o) u R.witness.bulk
  have hright : ∀j:Fin (SelectedTemplate k L l).length,
      ((SelectedTemplate k L l).get j).role≠.bulk →
      (permuteAssignment C σ (fibreAssignment C (outerNonbulk C l p o) u) j).val=
      (permuteAssignment C σ (fibreAssignment C (outerNonbulk C l p o) R.witness.bulk) j).val := by
    rw [permute_fibreAssignment (l:=l) C σ,permute_fibreAssignment (l:=l) C σ]
    exact fibreAssignment_nonbulk_fixed (l:=l) C _ _ _
  unfold rawBTerm squareBTerm
  rw [dite_eq_left hu]
  exact masked_prime_eq_squareBFactor (l:=l) (R.frame (l:=l) hcell hprime)
    (fibreAssignment C (outerNonbulk C l p o) u) (R.squareSource_mass (l:=l) u hu)
    p R.data.blockDraw (by exact R.blockReference.slot_values)
    had hout hV σ (permuteAssignment C σ (fibreAssignment C (outerNonbulk C l p o) u))
    hfreq (bulkSamples_permuted (bulkSize k L/2) k l C.bulk
      (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ _)
    hleft hright

theorem rawBTerm_mixed_eq_squareBTerm (corrected : Bool) (u : SelectedBulkSample C l)
    (hu : (selectedBulkPrior C l).mass u≠0) :
    R.rawBTerm (l:=l) hcell hprime corrected true u=R.squareBTerm (l:=l) hcell hprime had hout hV corrected true u := by
  have hleft := fibreAssignment_nonbulk_fixed (l:=l) C (outerNonbulk C l p o) u R.witness.bulk
  have hright : ∀j:Fin (SelectedTemplate k L l).length,
      ((SelectedTemplate k L l).get j).role≠.bulk →
      (permuteAssignment C σ (fibreAssignment C (outerNonbulk C l p o) u) j).val=
      (permuteAssignment C σ (fibreAssignment C (outerNonbulk C l p o) R.witness.bulk) j).val := by
    rw [permute_fibreAssignment (l:=l) C σ,permute_fibreAssignment (l:=l) C σ]
    exact fibreAssignment_nonbulk_fixed (l:=l) C _ _ _
  unfold rawBTerm squareBTerm
  rw [dite_eq_left hu]
  exact masked_mixed_eq_squareBFactor (l:=l) (R.frame (l:=l) hcell hprime)
    (fibreAssignment C (outerNonbulk C l p o) u) (R.squareSource_mass (l:=l) u hu)
    p R.data.blockDraw (by exact R.blockReference.slot_values)
    had hout hV σ (permuteAssignment C σ (fibreAssignment C (outerNonbulk C l p o) u))
    hfreq (bulkSamples_permuted (bulkSize k L/2) k l C.bulk
      (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ _)
    hleft hright corrected

theorem mean_rawBTerm_prime_eq_squareBTerm :
    (selectedBulkPrior C l).cmean (R.rawBTerm (l:=l) hcell hprime false false)=
      (selectedBulkPrior C l).cmean (R.squareBTerm (l:=l) hcell hprime had hout hV false false) := by
  apply FinitePrior.cmean_congr_support
  exact R.rawBTerm_prime_eq_squareBTerm hcell hprime had hout hV hfreq

theorem mean_rawBTerm_mixed_eq_squareBTerm (corrected : Bool) :
    (selectedBulkPrior C l).cmean (R.rawBTerm (l:=l) hcell hprime corrected true)=
      (selectedBulkPrior C l).cmean (R.squareBTerm (l:=l) hcell hprime had hout hV corrected true) := by
  apply FinitePrior.cmean_congr_support
  exact R.rawBTerm_mixed_eq_squareBTerm hcell hprime had hout hV hfreq corrected

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
