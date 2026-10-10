import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacementFrameDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacementFrame
open Construction Conclusion Filter ScaleBudget HistoryPairBulkTransport
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkGoodPatternPrincipalFrame HistoryBulkGiantCorrectedBounds
open HistoryBulkFibreIntegralReplacement HistoryBulkIntegralReplacement
open HistoryBulkReferenceScalarCoordinates HistoryPrincipalIntegralAverage

theorem selected_bulkMean_error_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hBs : 0≤Bs) (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀spectator : PrimeSource,
      (∀p:spectator.Sample,Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀ds : Fin (2*(bulkSize k L/2))→spectator.Sample,
    ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
    ∀l≤k,∀r : Frame (l:=l) C (spectatorList spectator ds),
    ∀(corrected mixed : Bool)(a : SelectedNonbulkSample C l)
      (σ : Equiv.Perm (Frame.Slots (depth:=k) (L:=L) (l:=l)))
      (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q),
      (corrected=true → l<k) →
      ‖bulkMean r corrected mixed a σ hV-principalOperator r corrected mixed σ hV‖≤
        192*Real.exp (-Real.exp (bulk.target*L)) := by
  filter_upwards [reference_plain_prime_error_eventually d Bs BD Bz hBs hk,
    reference_plain_mixed_error_eventually d Bs BD Bz hBs hk,
    reference_corrected_prime_error_eventually d Bs BD Bz hBs hk,
    reference_corrected_mixed_error_eventually d Bs BD Bz hBs hk]
    with L hpp hpm hcp hcm
  intro spectator hspec ds E C hblock hcenter l hl r corrected mixed a σ hV hstage
  cases corrected <;> cases mixed
  · obtain ⟨_,hb⟩ := hpp spectator hspec ds E C hblock hcenter l hl
      σ r.leftSource r.rightSource r.s r.t r.P r.Q r.leftChoices r.rightChoices
      r.left_mass r.right_mass r.left_choices_mass r.right_choices_mass
      r.plus_pos r.minus_pos r.plus_cell r.minus_cell
      r.left_supported r.right_supported r.matching (orderedBulkEquiv r) hV true a
    exact hb
  · obtain ⟨_,hb⟩ := hpm spectator hspec ds E C hblock hcenter l hl
      σ r.leftSource r.rightSource r.s r.t r.P r.Q r.leftChoices r.rightChoices
      r.left_mass r.right_mass r.left_choices_mass r.right_choices_mass
      r.plus_pos r.minus_pos r.plus_cell r.minus_cell
      r.left_supported r.right_supported r.matching (orderedBulkEquiv r) hV true a
    exact hb
  · obtain ⟨_,hb⟩ := hcp spectator hspec ds E C hblock hcenter l (hstage rfl)
      σ r.leftSource r.rightSource r.s r.t r.P r.Q r.leftChoices r.rightChoices
      r.left_mass r.right_mass r.left_choices_mass r.right_choices_mass
      r.plus_pos r.minus_pos r.plus_cell r.minus_cell
      r.left_supported r.right_supported r.matching (orderedBulkEquiv r) hV true a
    exact hb
  · obtain ⟨_,hb⟩ := hcm spectator hspec ds E C hblock hcenter l (hstage rfl)
      σ r.leftSource r.rightSource r.s r.t r.P r.Q r.leftChoices r.rightChoices
      r.left_mass r.right_mass r.left_choices_mass r.right_choices_mass
      r.plus_pos r.minus_pos r.plus_cell r.minus_cell
      r.left_supported r.right_supported r.matching (orderedBulkEquiv r) hV true a
    exact hb

end Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacementFrame

end

end OAI
