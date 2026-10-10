import OAI.NumberTheory.Jacobsthal.Estimates.RepeatedPositionNeighbors
import OAI.NumberTheory.Jacobsthal.Probability.RepeatedWordEvents

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CompactPositionRepetition
open FinitePathGeometry PrimeHistories RepeatedWordEvents RepeatedPositionNeighbors
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem compact_position_repetition {n : ℕ} (lab : ℕ → Fin n) (w L : ℝ) (z : Node)
    (pre tail : List ℕ) (p : ℕ)
    (hord : ((pre++p::tail).map lab).Pairwise (· ≥ ·))
    (hc : 2 ≤ ((pre++p::tail).map lab).count (lab p))
    (hgap : (terminal w z pre).gap ≤ L) (hp : 0 ≤ primeExponent w p) :
    compactAdjacentWord w lab L z (pre++p::tail) := by
  rcases repeated_position_neighbor lab pre tail p hord hc with ⟨pre',q,hpre,hq⟩ | ⟨q,tail',htail,hq⟩
  · refine ⟨pre',q,p,tail,?_,hq,?_⟩
    · rw [hpre]
      simp
    · rwa [← hpre]
  · refine ⟨pre,p,q,tail',by rw [htail],hq.symm,?_⟩
    have hg : (terminal w z (pre++[p])).gap=(terminal w z pre).gap-primeExponent w p := by
      simp [terminal,step]
    rw [hg]
    linarith

theorem compact_position_singleton {n : ℕ} (lab : ℕ → Fin n) (w L : ℝ) (z : Node)
    (ps : List ℕ) (hord : (ps.map lab).Pairwise (· ≥ ·))
    (hno : ¬compactAdjacentWord w lab L z ps)
    (pre tail : List ℕ) (p : ℕ) (he : ps=pre++p::tail)
    (hgap : (terminal w z pre).gap ≤ L) (hp : 0 ≤ primeExponent w p) :
    (ps.map lab).count (lab p) ≤ 1 := by
  by_contra hc
  have hc' : 2 ≤ (ps.map lab).count (lab p) := by omega
  apply hno
  rw [he] at hord hc' ⊢
  exact compact_position_repetition lab w L z pre tail p hord hc' hgap hp
end NumberTheoryLean.CompactPositionRepetition



namespace NumberTheoryLean.SourceCompactSingletons
open FinitePathGeometry PrimeHistories RepeatedWordEvents CompactPositionRepetition SortedLabelRepetition
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem source_compact_singleton {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (L : ℝ) (z : Node) (ps : List ℕ) (hd : ps.Pairwise (· > ·))
    (hsrc : ∀ p ∈ ps,p ∈ sourcePrimeSet w top)
    (hno : ¬compactAdjacentWord w (label (zero_lt_one.trans hw) htop hxi) L z ps)
    (pre tail : List ℕ) (p : ℕ) (he : ps=pre++p::tail) (hgap : (terminal w z pre).gap ≤ L) :
    (ps.map (label (zero_lt_one.trans hw) htop hxi)).count (label (zero_lt_one.trans hw) htop hxi p)=1 := by
  have hp : p ∈ ps := by rw [he]; simp
  have hp' := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hsrc p hp)
  have hxp : 0 ≤ primeExponent w p := by
    unfold primeExponent
    exact div_nonneg (Real.log_nonneg (le_trans hw.le hp'.2.1.le)) (Real.log_nonneg hw.le)
  have hle := compact_position_singleton _ w L z ps
    (source_word_labels_ordered hw htop hxi ps hd hsrc) hno pre tail p he hgap hxp
  have hpos : 0 < (ps.map (label (zero_lt_one.trans hw) htop hxi)).count (label (zero_lt_one.trans hw) htop hxi p) :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩)
  omega

theorem source_search_singleton {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (ps : List ℕ) (hno : ¬searchRepeatedWord hw htop hxi ps)
    (b : Fin (binCount w top xi)) (hs : ActualSourceTags.searchBin w (LogarithmicBinEndpoints.lower w top xi b))
    (hm : b ∈ ps.map (label (zero_lt_one.trans hw) htop hxi)) :
    (ps.map (label (zero_lt_one.trans hw) htop hxi)).count b=1 := by
  have hc := List.count_pos_iff.mpr hm
  have hn : ¬2 ≤ (ps.map (label (zero_lt_one.trans hw) htop hxi)).count b := fun h => hno ⟨b,hs,h⟩
  omega
end NumberTheoryLean.SourceCompactSingletons


end Erdos970

end OAI
