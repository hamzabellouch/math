import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualIntegralReplacementPlainDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualIntegralReplacement
open Construction Conclusion Filter
open HistoryBulkSourceDisintegration HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualGoodPrincipal HistoryBulkPatternIntegralReplacement
open HistoryBulkSupportConverse
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem selected_plain_bulk_error_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
    ∀spectator : PrimeSource,
      (∀p:spectator.Sample,Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
        Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
    ∃hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator,
    ∀ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,∀(l : ℕ)(hl : l ≤ k),
    ∃hV : ∀q∈spectatorList spectator ds,∀j ≤ l,frequencyBound Bs BD Bz k L j<q,
    ∀(σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))(mixed : Bool),
      ‖plainBulkPrincipal C spectator ds hactual hl σ mixed hV-
        plainPrincipal C spectator ds hactual hl σ mixed hV‖ ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖plainBulkPrincipal C spectator ds hactual hl σ mixed hV-
        plainPrincipal C spectator ds hactual hl σ mixed hV‖ ≤
          Real.exp (-H*(bulkSize k L:ℝ)) :=
  (((selected_background_bulk_error_eventually d Bs BD Bz H hBs hH hk).and
    (HistoryBulkFixedReferenceTerm.selected_reference_equality_eventually d Bs BD Bz
      (lt_of_lt_of_le (Nat.zero_lt_succ 1) hk))).and
    (selected_source_inputs_eventually d Bs BD Bz (lt_of_lt_of_le (Nat.zero_lt_succ 1) hk))).mono
    (fun L h E C hG hGu hcl hcu hb hd spectator hspec=>
      let hactual := h.1.2 E C hG hcl hcu hb hd spectator hspec
      let hout := (h.2 E C hG hcl hcu hb hd spectator hspec).2.2
      ⟨hactual,fun ds l hl=>
        let hV : ∀q∈spectatorList spectator ds,∀j ≤ l,frequencyBound Bs BD Bz k L j<q :=
          fun _q hq j hj=>Exists.elim (List.mem_ofFn.mp hq)
            (fun i hi=>hi ▸ hout (ds i) j (hj.trans hl))
        ⟨hV,fun σ mixed=>h.1.1 spectator (fun p=>(hspec p).2) ds E C hG hGu hcl hcu hb hd l hl
          false mixed hV (fun hf=>False.elim (Bool.false_ne_true hf))
          (fun bg p b=>plainPatternFamily C spectator ds hactual hl σ mixed p
            (restoreOuterBackground C l p bg b))⟩⟩)

end Ostmann.Arithmetic.HistoryBulkActualIntegralReplacement

end

end OAI
