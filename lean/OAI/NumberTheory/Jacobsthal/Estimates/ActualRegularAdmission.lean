import OAI.NumberTheory.Jacobsthal.Partitions.RegularityDefectPartition

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualRegularAdmission
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualWordSelection ActualRegularBoxes
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open SafeSubsetBoxGeometry ReferenceAdmission ActualSourceTags FiniteFirstTag
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem regular_word_reference {w top xi Clen B K : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ Clen) (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*(xi/Real.log w) ≤ 6*(2*Clen*xi)) (z : Node) (ps : List ℕ)
    (hp : ps ∈ regularWords hw htop hxi Clen B K z) :
    ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap := by
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hp).1
  have han := regular_word_anchor hw htop hxi hC hcomp hsmall z ps hp
  have hh := anchored_choice_geometry hw htop hxi hC hcomp z _ han
    (wordSelection (label (zero_lt_one.trans hw) htop hxi) ps)
    (wordSelection_mem hw htop hxi ps hd.2)
  rw [wordSelection_recovers _ ps hd.1] at hh
  exact hh.1

theorem regular_tag_singleton {Y w top xi Clen B K Cs eta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) (ps : List ℕ)
    (hp : ps ∈ regularWords hw htop hxi Clen B K z) (a : ℕ → ℤ)
    (t : Tag (binCount w top xi))
    (ht : sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a ps=some t) :
    (ps.map (label (zero_lt_one.trans hw) htop hxi)).count t.bin=1 := by
  obtain ⟨pre,p,tail,heq,_hidx,hbin,_hp,hsearch,_ho,_ha,_hn⟩ :=
    sourceTag_witness Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a ps ht
  have hmem : p ∈ ps := by rw [heq]; simp
  have hm : t.bin ∈ ps.map (label (zero_lt_one.trans hw) htop hxi) :=
    List.mem_map.mpr ⟨p,hmem,hbin.symm⟩
  have hpos := List.count_pos_iff.mpr hm
  rw [← hbin] at hsearch
  have hle := (Finset.mem_filter.mp hp).2.2.2.2 t.bin hsearch
  omega
end NumberTheoryLean.ActualRegularAdmission


end Erdos970

end OAI
