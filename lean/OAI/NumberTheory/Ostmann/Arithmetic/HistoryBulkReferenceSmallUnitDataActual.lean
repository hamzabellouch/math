import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceSmallUnitDataSource
import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceSmallUnitData
open Construction Conclusion DiagonalSmallResidueNorm HistoryPairBulkTransport Filter

theorem selected_smallUnitData_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
      ∀ (s : ℤ) (gp gm : ℕ)
        (x : SourceAssignment C.sources (Template.current seed l))
        (c : HistoryChoices C.sources seed V l)
        (outerU xs : List SmallSlot) (outside : List ℕ),
      (assignedHistory C.sources seed V l s gp gm x c).root.small.Perm (outerU++xs) →
      (assignmentPrior C.sources (Template.current seed l)).mass x ≠ 0 →
      s ≠ 0 → s.natAbs ≤ V l →
      ((assignedHistory C.sources seed V l s gp gm x c).root.small.map
        SmallSlot.value ++ outside).Pairwise Nat.Coprime →
      SmallUnitData outside.prod 1 1 outerU xs s := by
  filter_upwards [initial_sources_above_frequencies_eventually d Bs BD Bz hk] with L hfreq
  intro E C hblock hcenter hupper hbulk hspectator l hl
  dsimp only
  intro s gp gm x c outerU xs outside hslots hx hs hsv hstatic
  exact assigned_smallUnitData C.sources _ _ l s gp gm x c outerU xs outside hslots hx
    (hfreq E C hblock hcenter hupper hbulk hspectator l hl).2 hs hsv hstatic

end Ostmann.Arithmetic.HistoryBulkReferenceSmallUnitData

end

end OAI
