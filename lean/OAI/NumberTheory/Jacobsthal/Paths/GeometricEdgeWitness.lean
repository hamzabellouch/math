import OAI.NumberTheory.Jacobsthal.Estimates.CandidateExceptionMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GeometricEdgeWitness
open PrimeHistories GeometricRegularWords SourceCompactSingletons ActualWordSelection
open ErdosCofactorChoices ErdosSubsetWord BoundedCandidateCount BoundedEdgeBins FullBoxLengthBounds
open BinCutSelections BinCutPrefixGeometry SelectionWordSplit
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

theorem decreasing_edge_prefix_unique (ps pre tail pre' tail' : List ℕ) (u : ℕ)
    (hd : ps.Pairwise (· > ·)) (he : ps=pre++u::tail) (he' : ps=pre'++u::tail') : pre=pre' := by
  have hno : u ∉ pre := by
    intro hu
    have hh := hd
    rw [he,List.pairwise_append] at hh
    exact (lt_irrefl u) (hh.2.2 u hu u (by simp))
  have hno' : u ∉ pre' := by
    intro hu
    have hh := hd
    rw [he',List.pairwise_append] at hh
    exact (lt_irrefl u) (hh.2.2 u hu u (by simp))
  have hidx : ps.idxOf u=pre.length := by rw [he,List.idxOf_append_of_notMem hno]; simp
  have hidx' : ps.idxOf u=pre'.length := by rw [he',List.idxOf_append_of_notMem hno']; simp
  have hlen : pre.length=pre'.length := hidx.symm.trans hidx'
  calc
    pre=ps.take pre.length := by rw [he]; simp
    _=ps.take pre'.length := by rw [hlen]
    _=pre' := by rw [he']; simp

theorem geometric_word_bounded_edge {w top xi C B R L alpha beta M X : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℕ) (z : Node) (ps : List ℕ)
    (hp : ps ∈ geometricWords hw htop hxi C B R L alpha beta z)
    (pre tail : List ℕ) (u : ℕ) (he : ps=pre++u::tail)
    (hgap : (terminal w z pre).gap ≤ L)
    (hM : Real.log ((Y:ℝ)/(pre.prod:ℝ))/Real.log w ≤ M) (hX : primeExponent w u ≤ X) :
    boundedEdgeBin w top xi Y (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps) M X
      (label (zero_lt_one.trans hw) htop hxi u) := by
  have hreg := (Finset.mem_filter.mp hp).1
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hreg).1
  have hn : ps.Nodup := hd.1.imp (fun h => ne_of_gt h)
  let lab := label (zero_lt_one.trans hw) htop hxi
  let m := wordMultiplicity lab ps
  let f := wordSelection lab ps
  let j := lab u
  have hf : f ∈ selections (globalBins w top xi) m := wordSelection_mem hw htop hxi ps hd.2
  have hsingle := GeometricRegularWords.geometric_compact_singleton hw htop hxi z ps hp pre tail u he hgap
  have hcard : (f j).card=1 := (wordMultiplicity_count lab ps hn j).trans hsingle
  have hu : u ∈ f j := by
    change u ∈ ps.toFinset.filter (fun p => lab p=j)
    simp [he,j]
  obtain ⟨v,hfv⟩ := Finset.card_eq_one.mp hcard
  have huv : u=v := by simpa only [hfv,Finset.mem_singleton] using hu
  have hfu : f j={u} := by rwa [← huv] at hfv
  have hword := wordSelection_recovers lab ps hd.1
  have hsplit := selected_word_split hw htop hxi m f hf j u hfu
  rw [hword] at hsplit
  have hpre := decreasing_edge_prefix_unique ps pre tail (descendingWord (aboveSelection f j))
    (descendingWord (belowSelection f j)) u hd.1 he hsplit
  refine ⟨f,hf,u,hfu,?_,hX⟩
  unfold parentLength
  rw [← above_word_product hw htop hxi m f hf j,← hpre]
  exact hM
end NumberTheoryLean.GeometricEdgeWitness


end Erdos970

end OAI
