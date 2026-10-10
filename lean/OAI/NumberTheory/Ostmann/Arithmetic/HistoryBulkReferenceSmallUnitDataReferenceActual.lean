import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceSmallUnitDataActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceSmallUnitData
open Construction Conclusion DiagonalSmallResidueNorm HistoryPairBulkTransport Filter

theorem selected_smallUnitData_of_reference_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀ l : ℕ, l≤k →
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let V := frequencyBound Bs BD Bz k L
      ∀ (outside : List ℕ) (old : History l), old.Supported V outside →
      ∀ (gp gm : ℕ) (x : SourceAssignment C.sources (Template.current seed l))
        (c : HistoryChoices C.sources seed V l) (outerU xs : List SmallSlot),
      (assignedHistory C.sources seed V l old.root.frequency gp gm x c).root.small.Perm
        (outerU++xs) →
      (assignmentPrior C.sources (Template.current seed l)).mass x ≠ 0 →
      ((assignedHistory C.sources seed V l old.root.frequency gp gm x c).root.small.map
        SmallSlot.value ++ outside).Pairwise Nat.Coprime →
      SmallUnitData outside.prod 1 1 outerU xs old.root.frequency := by
  filter_upwards [selected_smallUnitData_eventually d Bs BD Bz hk] with L hunit
  intro E C hblock hcenter hupper hbulk hspectator l hl
  dsimp only
  intro outside old hold gp gm x c outerU xs hslots hx hstatic
  exact hunit E C hblock hcenter hupper hbulk hspectator l hl old.root.frequency gp gm
    x c outerU xs outside hslots hx (History.supported_root_frequency_ne_zero hold)
    (History.supported_root_frequency_bound hold) hstatic

end Ostmann.Arithmetic.HistoryBulkReferenceSmallUnitData

end

end OAI
