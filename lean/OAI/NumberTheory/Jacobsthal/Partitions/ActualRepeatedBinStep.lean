import OAI.NumberTheory.Jacobsthal.Estimates.FrozenSuffixData
import OAI.NumberTheory.Jacobsthal.Paths.MovingStopBandParameters

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CandidateTerminalGeometry
open FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate SourceStopWindow
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open MovingStopBandParameters FrozenSuffixData
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_ratio_div_cutoff (w : ℝ) (z : Node) (ps : List ℕ) (hne : ps ≠ [])
    (hx : (terminal w z ps).cutoff ≠ 0) :
    (terminal w z ps).ratio=(terminal w z ps).gap/(terminal w z ps).cutoff := by
  induction ps generalizing z with
  | nil => exact False.elim (hne rfl)
  | cons p ps ih =>
    cases ps with
    | nil =>
      change primeExponent w p ≠ 0 at hx
      change PrimeTiltGeometry.childRatio w z.gap p=(z.gap-primeExponent w p)/primeExponent w p
      unfold PrimeTiltGeometry.childRatio
      field_simp [hx]
    | cons q qs => exact ih (step w z p) (by simp) hx

theorem candidate_terminal_geometry (Y : ℕ) {w top Cs eta Clen B xi b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (hpos : 0 < b₀-xi/Real.log w)
    (hsmall : 2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*b₀)
    (residue : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) residue z ps) :
    b₀-xi/Real.log w ≤ (terminal w z ps).cutoff ∧ (terminal w z ps).cutoff ≤ b₁ ∧
      204/100 ≤ (terminal w z ps).ratio ∧ (terminal w z ps).ratio ≤ 218/100 ∧
      Consistent (terminal w z ps) ∧ (terminal w z ps).closed=false := by
  have hwin := candidate_actual_window Y hw htop hxi hC hcomp hsmall residue z ps hc
  have hx : 0 < (terminal w z ps).cutoff := hpos.trans_le hwin.1
  have hfrac := terminal_ratio_div_cutoff w z ps hc.1 hx.ne'
  have hlo : 204/100 ≤ (terminal w z ps).ratio := by rw [hfrac]; exact hwin.2.2.1
  have hhi : (terminal w z ps).ratio ≤ 218/100 := by rw [hfrac]; exact hwin.2.2.2
  have hcons : Consistent (terminal w z ps) := by
    apply (eq_div_iff (show (terminal w z ps).ratio ≠ 0 by linarith)).mpr
    have hh := (eq_div_iff hx.ne').mp hfrac
    nlinarith
  exact ⟨hwin.1,hwin.2.1,hlo,hhi,hcons,(terminal_suffix_cutoff w z z ps hc.1).2.1⟩
end NumberTheoryLean.CandidateTerminalGeometry



namespace NumberTheoryLean.ActualRepeatedBinStep
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership ActualPrimeHigh
open RepeatedBinGeometry CandidateTerminalGeometry MarkedPrefixTools
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem history_source_primes {w ell S top : ℝ} {start : Node}
    (hw : 1 < w) (htop : w < top) (hell : 1 ≤ ell) (hcap : w^start.cutoff=top)
    (h : History w ell S start) : ∀ p ∈ h.primes,p ∈ sourcePrimeSet w top := by
  intro p hp
  obtain ⟨hprime,hlo,hguard⟩ := allowed_prime_bounds hw h.admissible p hp
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast hprime.pos
  have hlow : w < (p:ℝ) := by
    simpa only [Real.rpow_one] using (lt_exponent_iff hw hp0).mp (hell.trans_lt hlo)
  have hupper : primeExponent w p ≤ start.cutoff := by
    cases he : start.closed with
    | false =>
      simp only [capGuard,he,Bool.false_eq_true,ite_false] at hguard
      exact hguard.le
    | true => simpa only [capGuard,he,ite_true] using hguard
  have hhigh := (exponent_le_iff hw hp0).mp hupper
  rw [hcap] at hhigh
  exact (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mpr ⟨hprime,hlow,hhigh⟩

theorem actual_same_bin_slack {w ell S top xi : ℝ} {start : Node}
    (hw : 1 < w) (htop : w < top) (hell : 1 ≤ ell) (hxi : 0 < xi)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hcap : w^start.cutoff=top)
    (h : History w ell S start) (hne : h.primes ≠ []) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node)
    (hl : label (zero_lt_one.trans hw) htop hxi (h.primes.getLastD 0)=label (zero_lt_one.trans hw) htop hxi p) :
    0 ≤ (h.append p hp).node.ratio-(h.node.ratio-1) ∧
      (h.append p hp).node.ratio-(h.node.ratio-1) ≤ h.node.ratio*(xi/Real.log w)/primeExponent w p := by
  have hLast : h.primes.getLastD 0 ∈ h.primes := by
    have he : h.primes.getLastD 0=h.primes.getLast hne := by
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hne
  have hsrcOld := history_source_primes hw htop hell hcap h _ hLast
  have hsrcNew := history_source_primes hw htop hell hcap (h.append p hp) p (by simp [History.append_primes])
  have hdist := equal_label_exponent_distance hw htop hxi hsrcOld hsrcNew hl
  have hdata := (mem_children_iff hw h.node.side h.node.closed p).mp hp
  have hx : 0 < primeExponent w p := by linarith [hdata.2.1]
  have hcut : primeExponent w p ≤ h.node.cutoff := by
    have hh := hdata.2.2.1
    cases he : h.node.closed with
    | false =>
      simp only [capGuard,he,Bool.false_eq_true,ite_false] at hh
      exact hh.le
    | true => simpa only [capGuard,he,ite_true] using hh
  have hlastCut : h.node.cutoff=primeExponent w (h.primes.getLastD 0) := terminal_lastD w start h.primes hne
  have hOld : 0 < primeExponent w (h.primes.getLastD 0) := by linarith [hcut]
  have hratio : h.node.ratio=h.node.gap/primeExponent w (h.primes.getLastD 0) := by
    have hh := terminal_ratio_div_cutoff w start h.primes hne (show h.node.cutoff ≠ 0 by linarith [hcut])
    change h.node.ratio=h.node.gap/h.node.cutoff at hh
    rwa [hlastCut] at hh
  have hrg : 0 < h.node.gap := terminal_gap_positive (by linarith : 0 ≤ ell) hr hs h.admissible
  have hh := adjacent_ratio_slack hrg hx (show primeExponent w p ≤ primeExponent w (h.primes.getLastD 0) by linarith [hcut])
    ((le_abs_self _).trans hdist)
  rw [← hratio] at hh
  simpa only [History.append_node,step,childRatio] using hh
end NumberTheoryLean.ActualRepeatedBinStep


end Erdos970

end OAI
