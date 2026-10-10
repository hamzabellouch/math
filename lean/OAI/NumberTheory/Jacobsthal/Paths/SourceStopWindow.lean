import OAI.NumberTheory.Jacobsthal.Probability.SourceMarkedStopping

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceStopWindow
open FinitePathGeometry PrimeHistories SourceStopPredicate RepresentativeAdmission RepresentativeStopGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open MarkedPrefixTools ErdosInversePrimeBin ErdosPrimeInputs.HarmonicPrimeMeasure

theorem candidate_source_primes (Y : ℕ) {w top Cs eta Clen B xi b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a z ps) :
    ∀ p ∈ ps,p ∈ sourcePrimeSet w top := by
  intro p hp
  exact (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mpr
    (bin_prime_in_source (zero_lt_one.trans hw) htop hxi _ (hc.2.2.1 p hp))

theorem candidate_actual_window (Y : ℕ) {w top Cs eta Clen B xi b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*b₀)
    (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a z ps) :
    b₀-xi/Real.log w ≤ (terminal w z ps).cutoff ∧ (terminal w z ps).cutoff ≤ b₁ ∧
      204/100 ≤ (terminal w z ps).gap/(terminal w z ps).cutoff ∧
      (terminal w z ps).gap/(terminal w z ps).cutoff ≤ 218/100 := by
  let rep := representative w (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi)
  have hsource := candidate_source_primes Y hw htop hxi a z ps hc
  have hlast : ps.getLastD 0 ∈ ps := by
    have he : ps.getLastD 0=ps.getLast hc.1 := by
      conv_lhs => rw [← List.dropLast_append_getLast hc.1]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hc.1
  have hp := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop _).mp (hsource _ hlast)
  have hx1 : 1 < primeExponent w (ps.getLastD 0) :=
    (one_lt_div (Real.log_pos hw)).mpr (Real.log_lt_log (zero_lt_one.trans hw) hp.2.1)
  have hx := source_representative_error hw htop hxi (hsource _ hlast)
  change 0 ≤ rep (ps.getLastD 0)-primeExponent w (ps.getLastD 0) ∧
    rep (ps.getLastD 0)-primeExponent w (ps.getLastD 0) ≤ xi/Real.log w at hx
  rw [← terminal_lastD w z ps hc.1] at hx hx1
  have hr := source_prefix_movement hw htop hxi hC hcomp z ps hsource hc.2.1
  change 0 ≤ (terminal w z ps).gap-representativeGap rep z.gap ps ∧
    (terminal w z ps).gap-representativeGap rep z.gap ps ≤ 2*Clen*xi at hr
  have hwin := hc.2.2.2.2.1
  exact representative_to_actual_window (r := (terminal w z ps).gap)
    (rrep := representativeGap rep z.gap ps) (x := (terminal w z ps).cutoff) (xrep := rep (ps.getLastD 0))
    (Delta := 2*Clen*xi) (h := xi/Real.log w) (by linarith) (by linarith [hx.1]) (by linarith [hx.2])
    (by linarith [hr.1]) (by linarith [hr.2]) hwin.1 hwin.2.1 hwin.2.2.1 hwin.2.2.2 hsmall
end NumberTheoryLean.SourceStopWindow

end

end Erdos970

end OAI
