import OAI.NumberTheory.Jacobsthal.Partitions.BinCutGapMovement

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualReferencePrefixes
open FinitePathGeometry PrimeHistories ReferenceAdmission StrongSourceFamilies StrongReferenceTransport
open PrimeBinMembership LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem reference_prefix_mem (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) (ps pre : List ℕ)
    (hp : ps ∈ referencePrefixes w P i r) (hpre : pre ∈ ps.inits) : pre ∈ referencePrefixes w P i r := by
  obtain ⟨tail,he⟩ := (List.mem_inits pre ps).mp hpre
  obtain ⟨hd,ha⟩ := Finset.mem_filter.mp hp
  obtain ⟨horder,hmem⟩ := mem_decreasingPrefixes.mp hd
  rw [← he] at horder ha
  apply Finset.mem_filter.mpr
  refine ⟨mem_decreasingPrefixes.mpr ⟨(List.pairwise_append.mp horder).1,?_⟩,
    ((admitted_append w r i pre tail).mp ha).1⟩
  intro p hp
  exact hmem p (by rw [← he]; exact List.mem_append_left _ hp)

theorem reference_prefix_gap_floor {w top : ℝ} (hw : 1 < w) (htop : w < top) (z : Node)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (ps pre : List ℕ)
    (hp : ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap) (hpre : pre ∈ ps.inits) :
    2 ≤ (terminal w z pre).gap :=
  (source_reference_transport hw htop z hs hz hg hclosed hcap pre (reference_prefix_mem w _ _ _ ps pre hp hpre)).2
end NumberTheoryLean.ActualReferencePrefixes



namespace NumberTheoryLean.SelectionWordSplit
open ErdosCofactorChoices ErdosSubsetWord BinCutSelections SourceLabelStrictOrder
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

theorem selected_word_split {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi))
    (u : ℕ) (hfu : f j={u}) :
    descendingWord f=descendingWord (aboveSelection f j)++u::descendingWord (belowSelection f j) := by
  have hu : u ∈ f j := by rw [hfu]; simp
  have hul := selected_prime_label hw htop hxi m f hf j hu
  have humem : u ∈ descendingWord f := (mem_descendingWord f u).mpr ⟨j,hu⟩
  have hsource := word_source_membership hw htop hxi m f hf
  have hsmaller : ∀ p ∈ descendingWord (belowSelection f j),p<u := by
    intro p hp
    have hh := (below_word_membership hw htop hxi m f hf j p).mp hp
    apply prime_lt_of_label_lt hw htop hxi (hsource p hh.1) (hsource u humem)
    rw [hul]
    exact hh.2
  have hgreater : ∀ p ∈ descendingWord (aboveSelection f j),u<p := by
    intro p hp
    have hh := (above_word_membership hw htop hxi m f hf j p).mp hp
    apply prime_lt_of_label_lt hw htop hxi (hsource u humem) (hsource p hh.1)
    rw [hul]
    exact hh.2
  have hright : (descendingWord (aboveSelection f j)++u::descendingWord (belowSelection f j)).Pairwise (· > ·) := by
    rw [List.pairwise_append,List.pairwise_cons]
    refine ⟨descendingWord_strict _,⟨hsmaller,descendingWord_strict _⟩,?_⟩
    intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hgreater a ha
    · exact (hsmaller b hb).trans (hgreater a ha)
  apply (descendingWord_strict f).eq_of_mem_iff hright
  intro p
  constructor
  · intro hp
    obtain ⟨k,hpk⟩ := (mem_descendingWord f p).mp hp
    have hpl := selected_prime_label hw htop hxi m f hf k hpk
    rcases lt_trichotomy k j with hlt | rfl | hgt
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ ((below_word_membership hw htop hxi m f hf j p).mpr ⟨hp,by rwa [hpl]⟩))
    · have he : p=u := by simpa only [hfu,Finset.mem_singleton] using hpk
      subst p
      simp
    · exact List.mem_append_left _ ((above_word_membership hw htop hxi m f hf j p).mpr ⟨hp,by rwa [hpl]⟩)
  · intro hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ((above_word_membership hw htop hxi m f hf j p).mp hp).1
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact humem
      · exact ((below_word_membership hw htop hxi m f hf j p).mp hp).1
end NumberTheoryLean.SelectionWordSplit



namespace NumberTheoryLean.BinCutPrefixGeometry
open ErdosCofactorChoices ErdosSubsetWord BinCutSelections SelectionWordSplit
open PrimeHistories PrimeProductLogCoordinates
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

theorem above_word_is_prefix {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi))
    (u : ℕ) (hfu : f j={u}) :
    descendingWord (aboveSelection f j) ∈ (descendingWord f).inits ∧
      descendingWord (aboveSelection f j)++[u] ∈ (descendingWord f).inits := by
  have he := selected_word_split hw htop hxi m f hf j u hfu
  constructor
  · exact (List.mem_inits _ _).mpr ⟨u::descendingWord (belowSelection f j),he.symm⟩
  · apply (List.mem_inits _ _).mpr
    refine ⟨descendingWord (belowSelection f j),?_⟩
    simpa only [List.append_assoc,List.singleton_append] using he.symm

theorem above_word_product {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) :
    (descendingWord (aboveSelection f j)).prod=selectionProduct (aboveSelection f j) := by
  apply descendingWord_product (globalBins w top xi)
    (fun i k hik => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi i k hik)
  intro k
  exact ((mem_selections _ _ _).mp (above_selection_mem _ m f hf j) k).1
end NumberTheoryLean.BinCutPrefixGeometry



namespace NumberTheoryLean.FullBoxPrefixLower
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport StrongSourceFamilies
open ErdosCofactorChoices ErdosSubsetWord SafeSubsetBoxGeometry ActualReferencePrefixes BinCutSelections BinCutPrefixGeometry
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

theorem full_box_child_gap_floor {w top xi B C K : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (z : Node)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m)
    (f : Fin (binCount w top xi) → Finset ℕ) (hf : f ∈ selections (globalBins w top xi) m)
    (j : Fin (binCount w top xi)) (u : ℕ) (hu : f j={u}) :
    2 ≤ (terminal w z (descendingWord (aboveSelection f j)++[u])).gap := by
  have hfull := (anchored_choice_geometry hw htop hxi hC hcomp z m ha f hf).1
  have hprefix := (above_word_is_prefix hw htop hxi m f hf j u hu).2
  exact reference_prefix_gap_floor hw htop z hs hz hg hclosed hcap _ _ hfull hprefix
end NumberTheoryLean.FullBoxPrefixLower


end Erdos970

end OAI
