import OAI.NumberTheory.Jacobsthal.Probability.RepeatedWordEvents

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedSelectedOccurrence
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain FiniteHistoryTransport
open ActualCoupledHistories RepeatedWordEvents RepeatedPairProbability RepeatedPairEvents
open FinitePairOccurrence CompactPrefixOccurrence SourceSelectedCompactOccupation
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels

variable {w ell S : ℝ} {start : Node}
variable (hwn : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hwn hell hS0 hS hr hsS in
theorem selected_repetition_probability {top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hcap : w^start.cutoff=top) (L mesh : ℝ) (N : ℕ) (E : Set (List ℕ))
    (hE : ∀ p : History w ell S start,p.primes ∈ E →
      searchRepeatedWord hw htop hxi p.primes ∨
      compactAdjacentWord w (label (zero_lt_one.trans hw) htop hxi) L start p.primes) :
    fullSourceLaw w ell S start hs mesh N {h | occurs E N h} ≤
      fullSourceLaw w ell S start hs mesh N
        (pairOccurrence (rawRepeatPair (label (zero_lt_one.trans hw) htop hxi) (w^((1/4:ℝ))) S Set.univ) N) +
      fullSourceLaw w ell S start hs mesh N
        (pairOccurrence (rawRepeatPair (label (zero_lt_one.trans hw) htop hxi) 1 L (compactParentGate L)) N) := by
  rw [fullSourceLaw_eq hwn hell hS0 hS hr hs hsS]
  apply le_trans (measure_mono_ae ?_) (measure_union_le _ _)
  filter_upwards [search_word_pair_occurs hwn hell hS0 hS hr hs hsS hw htop hxi hcap mesh N,
    compact_word_pair_occurs hwn hell hS0 hS hr hs hsS (label (zero_lt_one.trans hw) htop hxi) hw L mesh N] with h hsearch hcompact
  rintro ⟨j,hj⟩
  let k : Finset.Iic N := ⟨j.1,Finset.mem_Iic.mpr j.isLt.le⟩
  change selectedNode E ((h k).1.1) at hj
  cases hp : (h k).1.1 with
  | none => rw [hp] at hj; exact False.elim hj
  | some p =>
    rw [hp] at hj
    rcases hE p hj with hrep | hrep
    · exact Or.inl (hsearch k p hp hrep)
    · exact Or.inr (hcompact k p hp hrep)
end NumberTheoryLean.RepeatedSelectedOccurrence


end Erdos970

end OAI
