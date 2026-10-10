import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalPlain

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction Conclusion Filter HistoryBulkSourceDisintegration

theorem exists_plain_principal_budget (d : Decomposition) (Bs BD Bz H : ℝ)
    (hBs : 0 ≤ Bs) {k : ℕ} (hk : 2 ≤ k) (hH : 0 ≤ H) :
    ∃ ε : ℝ,0 < ε ∧ ∀ᶠ L : ℝ in atTop,∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
        Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      (∀p : spectator.Sample,(FiniteField.correlationBound (residueTransform d p.val):ℝ) ≤ ε) →
      ∀ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
      ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∃hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator,
      ∀l : ℕ,∀hl : l ≤ k,
      ∃hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q,
      ∀(σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))),
      ¬TransferBadArrangement σ → ∀mixed : Bool,
      ‖plainPrincipal C spectator ds hactual hl σ mixed hV‖ ≤
        Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) :=
  (exists_backgroundMean_budget d Bs BD Bz H hBs hk hH).elim fun ε hε =>
    ⟨ε,hε.1,(hε.2.and (HistoryBulkFixedReferenceTerm.selected_reference_equality_eventually
      d Bs BD Bz (lt_of_lt_of_le (Nat.succ_pos 1) hk))).mono fun _L hL =>
      fun spectator hband hflat ds E C hG hGu hc hcu hb hd =>
        let hactual := hL.2 E C hG hc hcu hb hd spectator hband
        ⟨hactual,fun l hl =>
          (hL.1 spectator hband hflat ds E C hG hGu hc hcu hb hd l hl).elim fun hV hbound =>
            ⟨hV,fun σ hgood mixed =>
              (congrArg norm (plainPrincipal_eq_backgroundMean C spectator ds hactual hl σ mixed hgood hV)).trans_le
                (hbound (fun p o=>plainGoodFamily C spectator ds hactual hl σ mixed p o hgood)
                  false mixed (fun h=>False.elim (Bool.false_ne_true h)))⟩⟩⟩

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
