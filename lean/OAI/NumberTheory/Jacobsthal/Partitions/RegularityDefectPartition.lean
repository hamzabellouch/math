import OAI.NumberTheory.Jacobsthal.Paths.ActualPrefixClearance
import OAI.NumberTheory.Jacobsthal.Probability.RepeatedWordEvents

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualRegularBoxes
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualPrefixClearance ActualWordSelection
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open SafeSubsetBoxGeometry ErdosSubsetWord ErdosCofactorChoices ActualSourceTags
open ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

noncomputable def regularWords {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Clen B K : ℝ) (z : Node) : Finset (List ℕ) :=
  (decreasingPrefixes (sourcePrimeSet w top)).filter (fun ps =>
    (ps.length:ℝ) ≤ Clen*Real.log B ∧ actualClearance w z (2*Clen*xi) ps ∧
    (terminal w z ps).gap ≤ K ∧ ∀ b,searchBin w (lower w top xi b) →
      (ps.map (label (zero_lt_one.trans hw) htop hxi)).count b ≤ 1)

noncomputable def regularBoxes {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Clen B K : ℝ) (z : Node) : Finset (Fin (binCount w top xi) → ℕ) :=
  (regularWords hw htop hxi Clen B K z).image
    (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi))

theorem regular_word_anchor {w top xi Clen B K : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ Clen) (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*(xi/Real.log w) ≤ 6*(2*Clen*xi)) (z : Node) (ps : List ℕ)
    (hp : ps ∈ regularWords hw htop hxi Clen B K z) :
    SafeAnchor hw htop hxi Clen B K z (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps) := by
  obtain ⟨hd,hlen,hclear,hgap,_hsingle⟩ := Finset.mem_filter.mp hp
  have hm := mem_decreasingPrefixes.mp hd
  refine ⟨wordSelection (label (zero_lt_one.trans hw) htop hxi) ps,
    wordSelection_mem hw htop hxi ps hm.2,?_⟩
  rw [wordSelection_recovers _ ps hm.1]
  exact ⟨hlen,clearance_supplies_safety hw htop hxi hC hcomp hsmall z ps hm.2 hlen hclear,hgap⟩

theorem regular_boxes_anchors {w top xi Clen B K : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ Clen) (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*(xi/Real.log w) ≤ 6*(2*Clen*xi)) (z : Node) :
    ∀ mult ∈ regularBoxes hw htop hxi Clen B K z,SafeAnchor hw htop hxi Clen B K z mult := by
  intro mult hm
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hm
  exact regular_word_anchor hw htop hxi hC hcomp hsmall z ps hps

theorem regular_boxes_search_singletons {w top xi Clen B K : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) :
    ∀ mult ∈ regularBoxes hw htop hxi Clen B K z,
      ∀ b ∈ occupiedSearch w top xi mult,mult b=1 := by
  intro mult hm b hb
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hd,_hlen,_hclear,_hgap,hsingle⟩ := Finset.mem_filter.mp hps
  have hn : ps.Nodup := (mem_decreasingPrefixes.mp hd).1.imp (fun h => ne_of_gt h)
  have hpos := (Finset.mem_filter.mp hb).2.2
  have hle := hsingle b (Finset.mem_filter.mp hb).2.1
  rw [wordMultiplicity_count _ ps hn] at hpos ⊢
  omega
end NumberTheoryLean.ActualRegularBoxes



namespace NumberTheoryLean.RegularityDefectPartition
open FinitePathGeometry PrimeHistories ActualRegularBoxes ActualPrefixClearance RepeatedWordEvents
open ReferenceAdmission LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
attribute [local instance] Classical.propDecidable

noncomputable def lengthFailure (C B : ℝ) (ps : List ℕ) : Prop := C*Real.log B < (ps.length:ℝ)
noncomputable def clearanceFailure (w Delta : ℝ) (z : Node) (ps : List ℕ) : Prop := ¬actualClearance w z Delta ps

theorem regularity_defect_sum {w top xi C B R : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (z : Node) (F : Finset (List ℕ))
    (hF : F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap)
    (hg : ∀ ps ∈ F,(terminal w z ps).gap ≤ R) :
    (∑ ps ∈ F \ regularWords hw htop hxi C B R z,prefixWeight ps) ≤
      (∑ ps ∈ F.filter (lengthFailure C B),prefixWeight ps) +
      (∑ ps ∈ F.filter (clearanceFailure w (2*C*xi) z),prefixWeight ps) +
      (∑ ps ∈ F.filter (searchRepeatedWord hw htop hxi),prefixWeight ps) := by
  simp only [Finset.sdiff_eq_filter,Finset.sum_filter]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ps hp
  have hnonneg := prefixWeight_nonneg ps
  by_cases hreg : ps ∈ regularWords hw htop hxi C B R z
  · simp only [hreg,not_true_eq_false,ite_false]
    positivity
  · have hf : lengthFailure C B ps ∨ clearanceFailure w (2*C*xi) z ps ∨ searchRepeatedWord hw htop hxi ps := by
      by_contra! hn
      apply hreg
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (hF hp)).1,?_,?_,hg ps hp,?_⟩
      · exact le_of_not_gt hn.1
      · exact not_not.mp hn.2.1
      · intro b hs
        by_contra hb
        exact hn.2.2 ⟨b,hs,by omega⟩
    simp only [hreg,not_false_eq_true,ite_true]
    split_ifs <;> simp_all
end NumberTheoryLean.RegularityDefectPartition


end Erdos970

end OAI
