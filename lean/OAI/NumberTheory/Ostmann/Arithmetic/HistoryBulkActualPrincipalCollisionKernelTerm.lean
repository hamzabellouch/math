import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionGuardAlgebra
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelExpansion
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkFibreOriginalReference HistoryPairRepresentatives HistoryPairKernelReplacement
open HistoryBulkReferencePeriodicMeanSource
attribute [local instance] Classical.propDecidable
attribute [local instance] kernelStageValueInternalDecidable
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
  (hout : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem kernelTerm_eq_guarded_product (symbolic corrected mixed : Bool)
    (u : SelectedBulkSample C l) :
    R.kernelTerm hcell hout hprime hV symbolic corrected mixed u =
      (R.kernelProduct hcell hprime symbolic mixed u:ℂ) *
      ((HistoryBulkActualGoodPrincipal.density (R.frame hcell hprime) mixed:ℂ) *
        (if ¬HistoryBulkPrincipalCollisionError.fibreSmallOutsideGuard C outside
          (outerNonbulk C l p o) u then 0 else
          (R.principalData hcell (bulkSize k L/2) hout hprime hV true).value corrected mixed u)) :=
  (R.kernelTerm_expansion hcell hout hprime hV symbolic corrected mixed u).trans
    ((R.frame hcell hprime).plain_guard_density_product σ (outerNonbulk C l p o) u mixed
      ((R.principalData hcell (bulkSize k L/2) hout hprime hV true).value corrected mixed u)
      (R.kernelProduct hcell hprime symbolic mixed u:ℂ))

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
