import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMixedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportActualPrincipalPlainMixed

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion Filter HistoryPairBulkTransport HistorySymbolicEncoding
open HistoryBulkReferencePeriodicMeanSource HistoryBulkGiantPrincipalTransport
open HistoryBulkReferenceNewModuli HistoryBulkSpectatorReferenceRaw
open HistoryBulkReferenceScalarCoordinates HistoryPairBulkCoordinates HistoryPairGiantCoordinates
open HistoryCRTIntegration HistoryBulkCorrectedXiBounds HistoryGiantXiReplacementActual
open HistoryBulkReferenceSmallMultiplier DiagonalSmallResidueNorm ScaleBudget

theorem frame_mixed_periodic_error_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    (hBs : 0≤Bs) {depth : ℕ} (hdepth : 0<depth) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz depth L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
    ∀ spectator : PrimeSource,
      (∀p:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀ ds : Fin (2*(bulkSize depth L/2))→spectator.Sample,
      (∀i,spectator.law.mass (ds i)≠0) →
    ∀ l≤depth, ∀r : Frame (l:=l) C (spectatorList spectator ds),
    ∀(σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
      (x y : Frame.Source (C:=C) (l:=l)),
      (assignmentPrior C.sources _).mass x≠0 →
      (∀i:Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length,
        ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).get i).role≠.bulk →
        (x i).val=(r.leftSource i).val) →
      ∀ hu : SmallUnitData (spectatorList spectator ds).prod 1 1
        (currentOuterSlots C x) (currentRemainingSlots C x) r.s,
      ‖r.periodicMixed σ x y hu-r.principalMixed σ x y‖≤9*Real.exp (-Real.exp (giant.target*L)) := by
  filter_upwards [plain_mixed_actual_principal_eventually d Bs BD Bz hBs hdepth,
    selected_newCRTCompatible_eventually d Bs BD Bz hdepth] with L hAP hCRT
  intro E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl r σ x y hx hfixed hu
  have hcrt := hCRT E C hG hcl hcu hb hd spectator hspec ds hds l hl
    x r.leftSource r.rightSource r.s r.s r.t 1 1 r.P r.Q
    r.leftChoices r.leftChoices r.rightChoices hx r.left_mass r.right_mass
    r.left_choices_mass r.right_choices_mass hfixed r.left_supported r.right_supported
  let := currentSmallPrimeFacts C x r.s r.leftChoices
  have ha := hAP E C hG hGu hcl hcu hb hd spectator (fun p=>(hspec p).2) ds l hl
    x r.leftSource r.rightSource r.s r.s r.t r.P r.Q 1 1
    r.leftChoices r.leftChoices r.rightChoices hx r.left_mass r.right_mass
    r.left_choices_mass r.right_choices_mass r.plus_pos r.minus_pos r.plus_cell r.minus_cell
    r.left_supported r.right_supported r.matching
    (Frame.Slots (depth:=depth) (L:=L) (l:=l))
    (orderedEquiv (2*(bulkSize depth L/2)) depth r.left r.right r.left_supported
      (root_matches (assignedLabels C.sources _ _ l r.s r.P.toNat r.Q.toNat r.leftSource r.leftChoices)))
    (orderedSourceValues C.sources (2*(bulkSize depth L/2)) depth l x)
    (by
      intro u
      unfold orderedSourceValues
      exact_mod_cast ((C.sources _).prime (x ((currentBulkPositionEquiv
        (2*(bulkSize depth L/2)) depth l).symm u).val).val
        (x ((currentBulkPositionEquiv (2*(bulkSize depth L/2)) depth l).symm u).val).property).pos)
    (r.newRight y) (2*(bulkSize depth L/2)) σ
    (sourceBulkUnits (frequencyModulus r.left r.right (depth+2)) C.sources
      (2*(bulkSize depth L/2)) depth l x) (r.fixedB x)
    (currentOuterSlots C x) (currentRemainingSlots C x)
    (currentSmallHistory_split C x r.s r.leftChoices)
    (spectatorList spectator ds).prod 1 1 r.s hu hcrt ∅ (by simp) C.giantPositive
  exact ha

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
