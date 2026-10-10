import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceSmallMultiplierActual

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceSmallMultiplier
open Construction Conclusion HistoryPairBulkTransport Filter
open HistoryGiantOriginalMeanFactorization HistoryDiagonalSmallOriginalMean
open HistoryBulkReferenceSmallUnitData DiagonalSmallResidueNorm HistoryCRTIntegration
open HistorySignedResidueFactorization HistorySignedResidueWeightedAverages

theorem selected_smallMultiplier_test_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l : ℕ, l ≤ k →
      ∀ (outside : List ℕ) (old : History l),
      old.Supported (frequencyBound Bs BD Bz k L) outside →
      ∀ (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
        (c : Choices (l:=l) C),
      (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).mass x ≠ 0 →
      ((currentSmallHistory C x old.root.frequency c).root.small.map SmallSlot.value ++ outside).Pairwise
        Nat.Coprime →
      ∃ hu : SmallUnitData outside.prod 1 1 (currentOuterSlots C x)
          (currentRemainingSlots C x) old.root.frequency,
        ∀ (P Q : ℤ), 0 ≤ P → 0 ≤ Q →
        (smallMultiplier C outside x old.root.frequency P Q : ℂ) *
          rootResidueIndicator (currentSmallHistory C x old.root.frequency c) (P,Q) =
        rootResidueIndicator (currentSmallHistory C x old.root.frequency c) (P,Q) *
          mixedExtension (currentRootSmallTest C outside x old.root.frequency c hu) (P,Q) := by
  filter_upwards [selected_smallUnitData_of_reference_eventually d Bs BD Bz hk] with L hunit
  intro E C hblock hcenter hupper hbulk hspectator l hl outside old hold x c hx hstatic
  have hu := hunit E C hblock hcenter hupper hbulk hspectator l hl outside old hold
    1 1 x c (currentOuterSlots C x) (currentRemainingSlots C x)
    (currentSmallHistory_split C x old.root.frequency c) hx hstatic
  refine ⟨hu, ?_⟩
  intro P Q hP hQ
  exact smallMultiplier_mul_currentRootIndicator C outside x old.root.frequency c hu P Q hP hQ

end Ostmann.Arithmetic.HistoryBulkReferenceSmallMultiplier

end

end OAI
