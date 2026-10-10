import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGoodPatternPrincipalFrameDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGoodPatternPrincipalFrame
open Construction Conclusion Filter HistoryPairPattern HistoryPairBulkTransport
open HistoryBulkFibreGiantApproximation HistoryBulkSelectedGoodOperator
open HistorySignedSpectatorCRT HistorySignedSpectatorDiagramAverage

theorem exists_principalOperator_budget (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0≤Bs) (hk : 0<k) (hH : 0≤H) :
    ∃ ε : ℝ, 0<ε ∧ ∀ᶠ L : ℝ in atTop, ∀ spectator : PrimeSource,
    (∀p : spectator.Sample, Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
      Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
    (∀p : spectator.Sample, (FiniteField.correlationBound (residueTransform d p.val):ℝ) ≤ ε) →
    ∀ ds : Fin (2*(bulkSize k L/2))→spectator.Sample,
    ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
    Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
    C.blockBase-2 < (C.giantCenter:ℝ) →
    (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
    |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
    |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
    ∀ (l : ℕ), l≤k →
    ∀ (r : Frame (l:=l) C (spectatorList spectator ds))
      (corrected mixed : Bool)
      (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
      (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q),
    (corrected=true → l<k) → ¬TransferBadArrangement σ →
    principalPayment Bs BD Bz L k l * ‖principalOperator r corrected mixed σ hV‖ ≤
      Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  obtain ⟨εp,hεp,hplain⟩ := reference_plain_good_operator_eventually d Bs BD Bz H hBs hk hH
  obtain ⟨εc,hεc,hcorrected⟩ := reference_corrected_good_operator_eventually d Bs BD Bz H hBs hk hH
  refine ⟨min εp εc,lt_min hεp hεc,?_⟩
  filter_upwards [hplain,hcorrected] with L hplain hcorrected
  intro spectator hband hflat ds E C hblock hcenter hupper hbulk hspectator
    l hl r corrected mixed σ hV hstage hgood
  have hpflat : ∀p : spectator.Sample,
      (FiniteField.correlationBound (residueTransform d p.val):ℝ) ≤ εp :=
    fun p=>(hflat p).trans (min_le_left _ _)
  have hcflat : ∀p : spectator.Sample,
      (FiniteField.correlationBound (residueTransform d p.val):ℝ) ≤ εc :=
    fun p=>(hflat p).trans (min_le_right _ _)
  cases corrected with
  | false =>
    have hb := hplain spectator hband hpflat ds E C hblock hcenter hupper hbulk hspectator
      l hl σ r.leftSource r.rightSource r.s r.t r.P r.Q r.leftChoices r.rightChoices
      r.left_mass r.right_mass r.left_choices_mass r.right_choices_mass
      r.plus_pos r.minus_pos r.plus_cell r.minus_cell
      r.left_supported r.right_supported r.matching (orderedBulkEquiv r) hV hgood
    cases mixed
    · have h := hb.1
      simp only [principalOperator,principalIntegral,Bool.false_eq_true,ite_false,
        Frame.left,Frame.right,assignedHistory,assignedRoot,
        HistorySignedXiTransport.giantState,HistoryGiantReferenceMean.sourceState] at h ⊢
      exact h
    · have h := hb.2
      simp only [principalOperator,principalIntegral,Bool.false_eq_true,ite_false,ite_true,
        Frame.left,Frame.right,assignedHistory,assignedRoot,
        HistorySignedXiTransport.giantState,HistoryGiantReferenceMean.sourceState] at h ⊢
      exact h
  | true =>
    have hb := hcorrected spectator hband hcflat ds E C hblock hcenter hupper hbulk hspectator
      l (hstage rfl) σ r.leftSource r.rightSource r.s r.t r.P r.Q r.leftChoices r.rightChoices
      r.left_mass r.right_mass r.left_choices_mass r.right_choices_mass
      r.plus_pos r.minus_pos r.plus_cell r.minus_cell
      r.left_supported r.right_supported r.matching (orderedBulkEquiv r) hV hgood
    cases mixed
    · have h := hb.1
      simp only [principalOperator,principalIntegral,ite_true,
        Frame.left,Frame.right,assignedHistory,assignedRoot,
        HistorySignedXiTransport.giantState,HistoryGiantReferenceMean.sourceState] at h ⊢
      exact h
    · have h := hb.2
      simp only [principalOperator,principalIntegral,ite_true,
        Frame.left,Frame.right,assignedHistory,assignedRoot,
        HistorySignedXiTransport.giantState,HistoryGiantReferenceMean.sourceState] at h ⊢
      exact h

end Ostmann.Arithmetic.HistoryBulkGoodPatternPrincipalFrame

end

end OAI
