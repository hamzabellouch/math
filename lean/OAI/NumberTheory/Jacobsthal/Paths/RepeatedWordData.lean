import OAI.NumberTheory.Jacobsthal.Probability.RepeatedPairProbability

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedWordData
open _root_.Set FinitePathGeometry PrimeHistories PrimeKilledChain PrimeTiltGeometry ActualPrimeHigh
open ActualRepeatedBinStep CandidateTerminalGeometry MarkedPrefixTools
open RepeatedPairEvents RepeatedPairProbability ActualSourceTags PrimeBinRepresentatives
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


variable {w ell S : ℝ} {start : Node}

theorem history_last_mem (h : History w ell S start) (hne : h.primes ≠ []) : h.primes.getLastD 0 ∈ h.primes := by
  have he : h.primes.getLastD 0=h.primes.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    exact List.getLastD_concat
  rw [he]
  exact List.getLast_mem hne

theorem history_nonempty_cutoff_gt (hw : 1 < w) (h : History w ell S start) (hne : h.primes ≠ []) :
    ell < h.node.cutoff := by
  have hh := (allowed_prime_bounds hw h.admissible _ (history_last_mem h hne)).2.1
  rwa [← terminal_lastD w start h.primes hne] at hh

theorem history_nonempty_ratio_le_gap (hw : 1 < w) (hell : 1 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (h : History w ell S start) (hne : h.primes ≠ []) : h.node.ratio ≤ h.node.gap := by
  have hx := history_nonempty_cutoff_gt hw h hne
  have hcut : 1 ≤ h.node.cutoff := hell.trans hx.le
  have hh := terminal_ratio_div_cutoff w start h.primes hne (by linarith : h.node.cutoff ≠ 0)
  change h.node.ratio=h.node.gap/h.node.cutoff at hh
  rw [hh]
  exact div_le_self (terminal_gap_positive (by linarith : 0 ≤ ell) hr hs h.admissible).le hcut

theorem search_prime_exponent {top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    {p : ℕ} (hp : p ∈ sourcePrimeSet w top)
    (hsearch : searchBin w (lower w top xi (label (zero_lt_one.trans hw) htop hxi p))) :
    w^((1/4:ℝ)) ≤ primeExponent w p := by
  have hp' := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp hp
  have hbin := label_prime_membership (zero_lt_one.trans hw) htop hxi hp'.1 hp'.2
  have hx := (bin_exponent_bounds hw (endpoint_pos (zero_lt_one.trans hw) _)
    (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le hbin).1
  exact hsearch.trans hx.le

theorem adjacent_search_pair_data {top xi : ℝ} (hw : 1 < w) (htop : w < top) (hell : 1 ≤ ell) (hxi : 0 < xi)
    (hsS : start.ratio ≤ S) (hcap : w^start.cutoff=top)
    (pre : List ℕ) (p q : ℕ) (a b : History w ell S start)
    (ha : a.primes=pre++[p]) (hb : b.primes=(pre++[p])++[q])
    (hl : label (zero_lt_one.trans hw) htop hxi p=label (zero_lt_one.trans hw) htop hxi q)
    (hsearch : searchBin w (lower w top xi (label (zero_lt_one.trans hw) htop hxi q))) :
    primeRepeatPair (label (zero_lt_one.trans hw) htop hxi) (w^((1/4:ℝ))) S Set.univ (some a,some b) := by
  have hna : a.primes ≠ [] := by rw [ha]; simp
  have hnb : b.primes ≠ [] := by rw [hb]; simp
  have hla : a.primes.getLastD 0=p := by rw [ha]; exact List.getLastD_concat
  have hlb : b.primes.getLastD 0=q := by rw [hb]; exact List.getLastD_concat
  have hsrc := history_source_primes hw htop hell hcap b q (by rw [hb]; simp)
  have hx := search_prime_exponent hw htop hxi hsrc hsearch
  have hcut : b.node.cutoff=primeExponent w q := by
    change (terminal w start b.primes).cutoff=primeExponent w q
    rw [terminal_lastD w start b.primes hnb,hlb]
  refine ⟨hna,terminal_ratio_le hsS a.admissible,Set.mem_univ _,?_,?_⟩
  · rw [hla,hlb]
    exact hl
  · rwa [hcut]

theorem adjacent_compact_pair_data {n : ℕ} (lab : ℕ → Fin n) (hw : 1 < w) (hell : 1 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (L : ℝ) (pre : List ℕ) (p q : ℕ) (a b : History w ell S start)
    (ha : a.primes=pre++[p]) (hb : b.primes=(pre++[p])++[q])
    (hl : lab p=lab q) (hgap : (terminal w start (pre++[p])).gap ≤ L) :
    primeRepeatPair lab 1 L (compactParentGate L) (some a,some b) := by
  have hna : a.primes ≠ [] := by rw [ha]; simp
  have hnb : b.primes ≠ [] := by rw [hb]; simp
  have hla : a.primes.getLastD 0=p := by rw [ha]; exact List.getLastD_concat
  have hlb : b.primes.getLastD 0=q := by rw [hb]; exact List.getLastD_concat
  have hga : a.node.gap ≤ L := by change (terminal w start a.primes).gap ≤ L; rwa [ha]
  have hratio := (history_nonempty_ratio_le_gap hw hell hr hs a hna).trans hga
  exact ⟨hna,hratio,hga,by rwa [hla,hlb],hell.trans (history_nonempty_cutoff_gt hw b hnb).le⟩
end NumberTheoryLean.RepeatedWordData


end Erdos970

end OAI
