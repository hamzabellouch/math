import OAI.NumberTheory.Jacobsthal.Partitions.SortedLabelRepetition
import OAI.NumberTheory.Jacobsthal.Paths.RepeatedWordData

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedWordEvents
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualPrimeHigh ActualProcessCoupling
open FiniteHistoryTransport FiniteHistoryOccurrence FiniteHistoryPairLaw FinitePairOccurrence
open ActualCoupledHistories RepeatedPairProbability RepeatedPairEvents RepeatedWordData
open SortedLabelRepetition AdjacentPrimeRecovery ActualRepeatedBinStep ActualSourceTags
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels


noncomputable def searchRepeatedWord {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (ps : List ℕ) : Prop := ∃ b : Fin (binCount w top xi),searchBin w (lower w top xi b) ∧
      2 ≤ (ps.map (label (zero_lt_one.trans hw) htop hxi)).count b

def compactAdjacentWord {n : ℕ} (w : ℝ) (lab : ℕ → Fin n) (L : ℝ) (start : Node) (ps : List ℕ) : Prop :=
  ∃ pre p q tail,ps=pre++p::q::tail ∧ lab p=lab q ∧ (terminal w start (pre++[p])).gap ≤ L

variable {w ell S : ℝ} {start : Node}
variable (hwn : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem search_word_pair_occurs {top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hcap : w^start.cutoff=top) (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N,
      ∀ j : Finset.Iic N,∀ p : History w ell S start,(h j).1.1=some p → searchRepeatedWord hw htop hxi p.primes →
      h ∈ pairOccurrence (rawRepeatPair (label (zero_lt_one.trans hw) htop hxi) (w^((1/4:ℝ))) S Set.univ) N := by
  filter_upwards [sourceHistory_recovers_adjacent hwn hell hS0 hS hr hs hsS mesh N] with h hh
  intro j p hp hrep
  obtain ⟨b,hsearch,hcount⟩ := hrep
  have hd := allowed_decreasing hw p.admissible
  have hsrc := history_source_primes hw htop hell hcap p
  obtain ⟨pre,a,c,tail,hword,ha,hc⟩ := source_repeated_label_adjacent hw htop hxi p.primes hd hsrc b hcount
  obtain ⟨k,q,r,hq,hr,hqw,hrw⟩ := hh j p hp pre a c tail hword
  apply Set.mem_iUnion.mpr
  refine ⟨k,?_⟩
  change primeRepeatPair _ _ _ _ ((atIndex N h k.castSucc).1.1,(atIndex N h k.succ).1.1)
  rw [hq,hr]
  apply adjacent_search_pair_data hw htop hell hxi hsS hcap pre a c q r hqw hrw (ha.trans hc.symm)
  rwa [hc]

theorem compact_word_pair_occurs {n : ℕ} (lab : ℕ → Fin n) (hw : 1 < w) (L mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N,
      ∀ j : Finset.Iic N,∀ p : History w ell S start,(h j).1.1=some p → compactAdjacentWord w lab L start p.primes →
      h ∈ pairOccurrence (rawRepeatPair lab 1 L (compactParentGate L)) N := by
  filter_upwards [sourceHistory_recovers_adjacent hwn hell hS0 hS hr hs hsS mesh N] with h hh
  intro j p hp hrep
  obtain ⟨pre,a,c,tail,hword,hlab,hgap⟩ := hrep
  obtain ⟨k,q,r,hq,hr',hqw,hrw⟩ := hh j p hp pre a c tail hword
  apply Set.mem_iUnion.mpr
  refine ⟨k,?_⟩
  change primeRepeatPair _ _ _ _ ((atIndex N h k.castSucc).1.1,(atIndex N h k.succ).1.1)
  rw [hq,hr']
  exact adjacent_compact_pair_data lab hw hell hr hs L pre a c q r hqw hrw hlab hgap
end NumberTheoryLean.RepeatedWordEvents


end Erdos970

end OAI
