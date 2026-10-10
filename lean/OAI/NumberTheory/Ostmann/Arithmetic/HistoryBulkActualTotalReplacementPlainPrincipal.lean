import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalPlainSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainDefs
import OAI.NumberTheory.Ostmann.Conclusion.LowLevelBadPairs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter
open HistoryBulkSourceDisintegration HistoryBulkActualTotalReplacement

theorem exists_plainFinalAverage_budget
    (d : Decomposition) (Bs BD Bz H : ℝ) (hBs : 0 ≤ Bs) {k : ℕ} (hk : 2 ≤ k) (hH : 0 ≤ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
        Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
        C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
        C.blockBase-2 < (C.giantCenter:ℝ) →
        (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
        |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
        |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
        ∀ spectator : PrimeSource,
        (∀ p : spectator.Sample, Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
          Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
        (∀ p : spectator.Sample,
          (FiniteField.correlationBound (residueTransform d p.val):ℝ) ≤ ε) →
        ∀ hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator,
        ∀ (j : ℕ) (hj : j ≤ k),
        ∃ hV : SpectatorResidueBounds C spectator j,
        ∀ (σ : Equiv.Perm (Fin (2^j) × Fin (2*(bulkSize k L/2)))),
          ¬TransferBadArrangement σ → ∀ mixed : Bool,
          ‖plainFinalAverage C spectator hactual hj σ mixed hV‖ ≤
            Real.exp (-H*(2:ℝ)^j*(bulkSize k L:ℝ)) :=
  (HistoryBulkActualGoodPrincipal.exists_plain_principal_budget
    d Bs BD Bz H hBs hk hH).elim fun ε hε =>
  ⟨ε,hε.1,hε.2.mono fun L hL => fun E C hG hGu hcl hcu hb hd spectator hspec hflat _hactual j hj =>
    let μ := spectatorPrior spectator (2*(bulkSize k L/2))
    let hpoint := fun ds : Fin (2*(bulkSize k L/2)) → spectator.Sample =>
      hL spectator hspec hflat ds E C hG hGu hcl hcu hb hd
    let hV : SpectatorResidueBounds C spectator j := fun ds =>
      ((hpoint ds).choose_spec j hj).choose
    ⟨hV,fun σ hgood mixed =>
      (μ.norm_cmean_le _).trans
        ((μ.mean_mono (fun ds =>
          ((hpoint ds).choose_spec j hj).choose_spec σ hgood mixed)).trans_eq
          (μ.mean_const _))⟩⟩

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
