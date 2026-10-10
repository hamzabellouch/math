import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReplacementErrorAP
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReplacementErrorCells
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReplacementErrorVariation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkRestorationError

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReplacementError
open Construction Conclusion HistoryBulkPriorGrid PrimeCellReplacement PrimeProgression
open ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget LogCellPartition Filter
open scoped BigOperators

theorem eventually_bulk_replacement_error_budget (k : ℕ) (C : ℝ)
    {K d : ℝ} (hK : 0 ≤ K) (hd : 0 < d) :
    ∀ᶠ L : ℝ in atTop, ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀(M a:ℕ)(E:Finset ℕ)(D A H R:ℝ),
      Fintype.card ι ≤ 2^k*bulkSize k L → a ≤ residueCostExponent k →
      0 < M → Real.log (M:ℝ) ≤ Real.exp (bulk.μ*L) → E.card ≤ 2 →
      0 ≤ D → 0 ≤ A → 0 ≤ H → 0 ≤ R →
      D ≤ Real.exp (C*((bulkSize k L:ℝ)+1)) → A ≤ Real.exp (C*((bulkSize k L:ℝ)+1)) →
      H ≤ (M:ℝ)^(Fintype.card ι+a)*Real.exp (C*((bulkSize k L:ℝ)+1)) →
      R ≤ (M:ℝ)^(Fintype.card ι+a) →
    (bulkFullMassRatio L E^Fintype.card ι-1)*H+
      (2*((Fintype.card ι:ℝ)*D*meshWidth bulk L)*
          principalMass M (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
            (fun _ => bulkNormalizer L E)+
        ((Fintype.card ι:ℝ)*D*meshWidth bulk L+A)*
          (Fintype.card (GridBoxIndex (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
            (fun _ => meshWidth bulk L))*
              ((Fintype.card ι:ℝ)*primeEnvelope bulk k 1 K d L*2^Fintype.card ι)))*R ≤
      3*Real.exp (-Real.exp (bulk.target*L)) := by
  filter_upwards [eventually_bulk_ap_error k C hK hd,eventually_bulk_variation_error k C,
    HistoryBulkRestorationError.bulk_restoration_error_eventually k C,
    bulkNormalizer_bounds_eventually,eventually_ge_atTop (0:ℝ)]
    with L hap hvar hrestore hnorm hL
  intro ι _ _ M a E D A H R hn ha hM hmod hE hD hA hH hR hDb hAb hHb hRb
  have hn' : Fintype.card ι ≤ 2^k*bulkSize k L+2 := by omega
  have hv := hvar ι M a E D hn' ha hM hmod hE hD hDb
  have he := hap ι M a D A hn' ha hM hmod hD hA hDb hAb
  have hr := hrestore E (Fintype.card ι) a M H hE hn ha hM hmod hH hHb
  have hz := hnorm E hE
  have hp := (bulk_principalMass_bounds (ι:=ι) M hM hL E hz.1 hz.2.1).1
  have henv : 0 ≤ primeEnvelope bulk k 1 K d L := by unfold primeEnvelope; positivity
  have hv' := (mul_le_mul_of_nonneg_left hRb
    (show 0 ≤ 2*((Fintype.card ι:ℝ)*D*meshWidth bulk L)*
      principalMass M (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
        (fun _ => bulkNormalizer L E) by unfold meshWidth; positivity)).trans hv
  have he' := (mul_le_mul_of_nonneg_left hRb
    (show 0 ≤ ((Fintype.card ι:ℝ)*D*meshWidth bulk L+A)*
      (Fintype.card (GridBoxIndex (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
        (fun _ => meshWidth bulk L))*
          ((Fintype.card ι:ℝ)*primeEnvelope bulk k 1 K d L*2^Fintype.card ι)) by
      unfold meshWidth; positivity)).trans he
  nlinarith only [hr,hv',he']

end Ostmann.Arithmetic.HistoryBulkReplacementError

end

end OAI
