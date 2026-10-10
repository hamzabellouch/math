import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkDiagramFrequencyAverageActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacementTests

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacement
open Construction ResidueHaar HistoryBulkResidueRootAverage HistoryBulkDiagramFrequencyAverage
open HistoryPairedFrequencyAverage HistorySignedSpectatorDiagramAverage HistoryRepresentativeSourceSeparation
open HistoryFrequencyResidues HistoryBulkSpectatorProduct HistoryBulkReplacementGeometry HistoryBulkResidueNormSum
open scoped BigOperators
variable (d : Decomposition) {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
  (h g : History l) (hs : h.Supported V outside) (gs : g.Supported V outside)
  (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
  (σ : Equiv.Perm (Fin (2^l)×Fin m)) (K : ℕ)
  (had : PairAdmissible h g outside) (hm : 0 < m) (hthree : ∀q∈outside,3 ≤ q)

include had hm hthree

theorem rootTest_canonical_unit_average_le :
    letI : NeZero (bulkModulus h g outside K) := ⟨actual_bulk_modulus_ne_zero h g hs gs hp K⟩
    letI : NeZero (pairedFrequencyProduct h g) := ⟨pairedFrequencyProduct_ne_zero hs gs⟩
    ‖average (rootTest false false d h g hs gs hp hV σ K)‖ ≤
      (((3:ℝ)^(2^l))^outside.length)*canonicalUnitBulkAverage K h g hs gs m := by
  let : NeZero (bulkModulus h g outside K) := ⟨actual_bulk_modulus_ne_zero h g hs gs hp K⟩
  let : NeZero outside.prod := ⟨(HistoryCRTIntegration.outsideModulus_pos hp).ne'⟩
  let : NeZero (pairedFrequencyProduct h g) := ⟨pairedFrequencyProduct_ne_zero hs gs⟩
  change ‖average (canonicalUnit d h g hs gs hp hV σ K)‖ ≤ _
  rw [average_canonicalUnit_eq_coupledAverage]
  exact actual_canonical_unit_universal d h g hs gs hp hV σ K had hm hthree

theorem rootTest_canonical_mixed_average_le :
    letI : NeZero (bulkModulus h g outside K) := ⟨actual_bulk_modulus_ne_zero h g hs gs hp K⟩
    letI : NeZero (pairedFrequencyProduct h g) := ⟨pairedFrequencyProduct_ne_zero hs gs⟩
    ‖average (rootTest false true d h g hs gs hp hV σ K)‖ ≤
      (((3:ℝ)^(2^l))^outside.length)*canonicalRingUnitBulkAverage K h g hs gs m := by
  let : NeZero (bulkModulus h g outside K) := ⟨actual_bulk_modulus_ne_zero h g hs gs hp K⟩
  let : NeZero outside.prod := ⟨(HistoryCRTIntegration.outsideModulus_pos hp).ne'⟩
  let : NeZero (pairedFrequencyProduct h g) := ⟨pairedFrequencyProduct_ne_zero hs gs⟩
  change ‖average (canonicalMixed d h g hs gs hp hV σ K)‖ ≤ _
  rw [average_canonicalMixed_eq_coupledAverage]
  exact actual_canonical_mixed_universal d h g hs gs hp hV σ K had hm hthree

theorem rootTest_independent_unit_average_le (hgood : ¬Conclusion.TransferBadArrangement σ) :
    letI : NeZero (bulkModulus h g outside K) := ⟨actual_bulk_modulus_ne_zero h g hs gs hp K⟩
    letI := primeAtNeZero hp
    ‖average (rootTest true false d h g hs gs hp hV σ K)‖ ≤
      ∏i : Fin outside.length, Tree.treeComparisonConstant (l-2)*
        ((FiniteField.correlationBound (residueTransform d (primeAt outside i)):ℝ)+
          (primeAt outside i:ℝ)^(-(1/4:ℝ))) := by
  let : NeZero (bulkModulus h g outside K) := ⟨actual_bulk_modulus_ne_zero h g hs gs hp K⟩
  let : NeZero outside.prod := ⟨(HistoryCRTIntegration.outsideModulus_pos hp).ne'⟩
  let : NeZero (pairedFrequencyProduct h g) := ⟨pairedFrequencyProduct_ne_zero hs gs⟩
  let := primeAtNeZero hp
  change ‖average (independentUnit d h g hs gs hp hV σ K)‖ ≤ _
  rw [average_independentUnit_eq_coupledAverage]
  exact actual_independent_unit_good d h g hs gs hp hV σ K had hm hthree hgood

theorem rootTest_independent_mixed_average_le (hgood : ¬Conclusion.TransferBadArrangement σ) :
    letI : NeZero (bulkModulus h g outside K) := ⟨actual_bulk_modulus_ne_zero h g hs gs hp K⟩
    letI := primeAtNeZero hp
    ‖average (rootTest true true d h g hs gs hp hV σ K)‖ ≤
      ∏i : Fin outside.length, Tree.treeComparisonConstant (l-2)*
        ((FiniteField.correlationBound (residueTransform d (primeAt outside i)):ℝ)+
          (primeAt outside i:ℝ)^(-(1/4:ℝ))) := by
  let : NeZero (bulkModulus h g outside K) := ⟨actual_bulk_modulus_ne_zero h g hs gs hp K⟩
  let : NeZero outside.prod := ⟨(HistoryCRTIntegration.outsideModulus_pos hp).ne'⟩
  let : NeZero (pairedFrequencyProduct h g) := ⟨pairedFrequencyProduct_ne_zero hs gs⟩
  let := primeAtNeZero hp
  change ‖average (independentMixed d h g hs gs hp hV σ K)‖ ≤ _
  rw [average_independentMixed_eq_coupledAverage]
  exact actual_independent_mixed_good d h g hs gs hp hV σ K had hm hthree hgood

end Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacement

end

end OAI
