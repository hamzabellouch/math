import OAI.NumberTheory.Jacobsthal.Paths.FullBoxPrefixLower

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FullBoxLengthBounds
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
open ErdosCofactorChoices ErdosSubsetWord BinCutSelections BinCutPrefixGeometry BinCutGapMovement
open SafeSubsetBoxGeometry FullBoxPrefixLower PrimeProductLogCoordinates
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition


noncomputable def parentLength (w : ℝ) (Y : ℕ) {n : ℕ} (f : Fin n → Finset ℕ) (j : Fin n) : ℝ :=
  Real.log ((Y:ℝ)/(selectionProduct (aboveSelection f j):ℝ))/Real.log w
noncomputable def childLength (w : ℝ) (Y : ℕ) {n : ℕ} (f : Fin n → Finset ℕ) (j : Fin n) (u : ℕ) : ℝ :=
  Real.log ((Y:ℝ)/((selectionProduct (aboveSelection f j):ℝ)*(u:ℝ)))/Real.log w

theorem parent_length_gap {w top xi a : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (hY : 0 < Y) (z : Node) (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) :
    parentLength w Y f j=(terminal w z (descendingWord (aboveSelection f j))).gap+a-2 := by
  have hsource := word_source_membership hw htop hxi _ _ (above_selection_mem _ m f hf j)
  have hg := terminal_gap_log_quotient Y hY z hroot (descendingWord (aboveSelection f j))
    (fun p hp => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hsource p hp)).1.pos)
  rw [above_word_product hw htop hxi m f hf j] at hg
  unfold parentLength
  linarith

theorem child_length_gap {w top xi a : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (hY : 0 < Y) (z : Node) (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) (u : ℕ) (hu : f j={u}) :
    childLength w Y f j u=(terminal w z (descendingWord (aboveSelection f j)++[u])).gap+a-2 := by
  have hfull := word_source_membership hw htop hxi m f hf
  have hpre := (above_word_is_prefix hw htop hxi m f hf j u hu).2
  have hsub : descendingWord (aboveSelection f j)++[u] ⊆ descendingWord f := by
    obtain ⟨tail,he⟩ := (List.mem_inits _ _).mp hpre
    intro p hp
    rw [← he]
    exact List.mem_append_left _ hp
  have hg := terminal_gap_log_quotient Y hY z hroot (descendingWord (aboveSelection f j)++[u])
    (fun p hp => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hfull p (hsub hp))).1.pos)
  rw [List.prod_append,List.prod_singleton,above_word_product hw htop hxi m f hf j,Nat.cast_mul] at hg
  unfold childLength
  linarith

theorem parent_length_movement {w top xi B C a : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ C) (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (m : Fin (binCount w top xi) → ℕ) (hlen : ((∑ k,m k : ℕ):ℝ) ≤ C*Real.log B)
    (f g : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (hg : g ∈ selections (globalBins w top xi) m)
    (j : Fin (binCount w top xi)) : |parentLength w Y f j-parentLength w Y g j| ≤ 2*C*xi := by
  rw [parent_length_gap hw htop hxi Y hY z hroot m f hf j,parent_length_gap hw htop hxi Y hY z hroot m g hg j]
  convert above_gap_movement hw htop hxi hC hcomp z m hlen f g hf hg j using 1
  congr 1
  ring

theorem full_box_child_length_lower {w top xi B C K a : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m)
    (f : Fin (binCount w top xi) → Finset ℕ) (hf : f ∈ selections (globalBins w top xi) m)
    (j : Fin (binCount w top xi)) (u : ℕ) (hu : f j={u}) : a ≤ childLength w Y f j u := by
  rw [child_length_gap hw htop hxi Y hY z hroot m f hf j u hu]
  have hh := full_box_child_gap_floor hw htop hxi hC hcomp z hs hz hg hclosed hcap m ha f hf j u hu
  linarith
end NumberTheoryLean.FullBoxLengthBounds



namespace NumberTheoryLean.BoundedEdgeBins
open ErdosCofactorChoices ErdosSubsetWord FullBoxLengthBounds
open FinitePathGeometry PrimeHistories SafeSubsetBoxGeometry
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

noncomputable def boundedEdgeBin (w top xi : ℝ) (Y : ℕ)
    (m : Fin (binCount w top xi) → ℕ) (M X : ℝ) (j : Fin (binCount w top xi)) : Prop :=
  ∃ f ∈ selections (globalBins w top xi) m,∃ u : ℕ,f j={u} ∧ parentLength w Y f j ≤ M ∧ primeExponent w u ≤ X

theorem bounded_edge_singleton {w top xi M X : ℝ} {Y : ℕ}
    (m : Fin (binCount w top xi) → ℕ) (j : Fin (binCount w top xi))
    (hj : boundedEdgeBin w top xi Y m M X j) : m j=1 := by
  obtain ⟨f,hf,u,hfu,_⟩ := hj
  have hh := ((mem_selections _ _ _).mp hf j).2
  simpa [hfu] using hh.symm

theorem anchor_total_length {w top xi B C K : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (z : Node) (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m) :
    ((∑ k,m k : ℕ):ℝ) ≤ C*Real.log B := by
  obtain ⟨g,hg,hlen,_⟩ := ha
  rwa [global_word_length hw htop hxi m g hg] at hlen
end NumberTheoryLean.BoundedEdgeBins


end Erdos970

end OAI
