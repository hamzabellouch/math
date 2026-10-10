import OAI.NumberTheory.Jacobsthal.Partitions.ActualBoxFourSum
import OAI.NumberTheory.Jacobsthal.Primes.BoundedEdgeHighPrimes
import OAI.NumberTheory.Jacobsthal.Primes.PaperMissingPrimeWindow
import OAI.NumberTheory.Jacobsthal.Probability.PaperSubsetTagEvent

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SubsetTagFailureMass
open ErdosCofactorChoices ErdosSubsetWord ErdosTagEvent ActualSourceTags ActualBinOwners
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels CanonicalSubsetBox
open WrongOwnerBinMass ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def badSelections {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) : Finset (Fin (binCount w top xi) → Finset ℕ) :=
  (selections (globalBins w top xi) mult).filter (fun f =>
    (∀ b ∈ occupiedSearch w top xi mult,∀ p ∈ f b,aligns a q p) ∧
    ¬∃ t,sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a (descendingWord f)=some t ∧ t.rational=q)

noncomputable def badMass {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) : ℝ :=
  ∑ f ∈ badSelections (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q,(selectionProduct f:ℝ)⁻¹

theorem bad_mass_le_alignment {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) :
    badMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q ≤
      ∑ f ∈ (selections (globalBins w top xi) mult).filter
        (fun f => ∀ b ∈ occupiedSearch w top xi mult,∀ p ∈ f b,aligns a q p),(selectionProduct f:ℝ)⁻¹ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro f hf
    obtain ⟨hf,ha,hbad⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨hf,ha⟩
  · intro f _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem bad_mass_le_wrong {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ)
    (howner : ∀ b ∈ occupiedSearch w top xi mult,
      nearFull eta (lower w top xi b) (width w top xi b) a q →
      owner Y w Cs eta (lower w top xi b) (width w top xi b) a=some q)
    (hnear : ∃ b ∈ occupiedSearch w top xi mult,
      nearFull eta (lower w top xi b) (width w top xi b) a q) :
    badMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q ≤
      ∑ f ∈ (selections (globalBins w top xi) mult).filter
        (fun f => ∃ b ∈ occupiedSearch w top xi mult,∃ p ∈ f b,
          p ∈ wrongOwnerPrimes Y w Cs eta (lower w top xi b) (width w top xi b) a q),(selectionProduct f:ℝ)⁻¹ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro f hf
    obtain ⟨hf,halign,hbad⟩ := Finset.mem_filter.mp hf
    have hh := subset_bad_tag_inclusion hw htop hxi mult f a q hf howner halign hbad
    rcases hh with hnone | hwrong
    · obtain ⟨b,hb,hn⟩ := hnear
      exact False.elim (hnone b hb hn)
    · exact Finset.mem_filter.mpr ⟨hf,hwrong⟩
  · intro f _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
end NumberTheoryLean.SubsetTagFailureMass



namespace NumberTheoryLean.HardTagBoxMass
open SubsetTagFailureMass ActualSourceTags ActualBinOwners
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels PrimeBinRepresentatives
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseAlignment
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

noncomputable def hardBadSelections {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) : Finset (Fin (binCount w top xi) → Finset ℕ) :=
  (selections (globalBins w top xi) mult).filter (fun f =>
    (∀ p ∈ descendingWord f,Cs < primeExponent w p → aligns a q p) ∧
    ¬∃ t,sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a (descendingWord f)=some t ∧ t.rational=q)

noncomputable def hardBadMass {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) : ℝ :=
  ∑ f ∈ hardBadSelections (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q,(selectionProduct f:ℝ)⁻¹

theorem hardBad_subset_bad {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hsearch : Cs ≤ w^((1/4:ℝ))) (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) :
    hardBadSelections (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q ⊆
      badSelections (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q := by
  intro f hf
  obtain ⟨hf,halign,hbad⟩ := Finset.mem_filter.mp hf
  refine Finset.mem_filter.mpr ⟨hf,?_,hbad⟩
  intro b hb p hp
  have hbin := ((mem_selections _ mult f).mp hf b).1 hp
  have hx := (bin_exponent_bounds hw (endpoint_pos (zero_lt_one.trans hw) _)
    (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le hbin).1
  have hs := (Finset.mem_filter.mp hb).2.1
  change w^((1/4:ℝ)) ≤ leftExponent w (lower w top xi b) at hs
  exact halign p ((mem_descendingWord f p).mpr ⟨b,hp⟩) (hsearch.trans hs |>.trans_lt hx)

theorem hardBadMass_le_badMass {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hsearch : Cs ≤ w^((1/4:ℝ))) (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) :
    hardBadMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q ≤
      badMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (hardBad_subset_bad hw htop hxi hsearch mult a q)
    (fun f _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
end NumberTheoryLean.HardTagBoxMass



namespace NumberTheoryLean.SafeAnchorSearchCount
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open StrongReferenceTransport StrongSourceFamilies SafeSubsetBoxGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open ErdosCofactorChoices ErdosSubsetWord ErdosSearchCount


theorem safe_anchor_search_count (K Clen : ℝ) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,∀ (top B xi : ℝ) (hw : 1 < w) (htop : w < top) (hxi : 0 < xi),
      xi ≤ 1 → Real.log B ≤ 2*Real.log w → ∀ z : Node,
      Valid z.side z.ratio → Consistent z → StrongState z → z.closed=true → w^z.cutoff=top → w ≤ z.gap →
      ∀ mult : Fin (binCount w top xi) → ℕ,SafeAnchor hw htop hxi Clen B K z mult →
      (∀ b ∈ occupiedSearch w top xi mult,mult b=1) →
      searchConstant*Real.log w ≤ ((occupiedSearch w top xi mult).card:ℝ) ∧
        (∑ b,(mult b:ℝ)) ≤ Clen*Real.log B := by
  filter_upwards [actual_search_count_uniform K Clen hC] with w hcount
  intro top B xi hw htop hxi hxi1 hcomp z hs hz hstrong hclosed hcap hstart mult ha hsingle
  obtain ⟨f,hf,hlen,hsafe,hK⟩ := ha
  have ha' : SafeAnchor hw htop hxi Clen B K z mult := ⟨f,hf,hlen,hsafe,hK⟩
  have href := (anchored_choice_geometry hw htop hxi hC hcomp z mult ha' f hf).1
  have htransport := source_reference_transport hw htop z hs hz hstrong hclosed hcap (descendingWord f) href
  obtain ⟨U,_hU,hallowed⟩ := (uncapped_iff_exists_ceiling w 1 z (descendingWord f)).mp
    ((mem_uncappedPrefixes hw z (descendingWord f)).mp htransport.1)
  have hsource := word_source_membership hw htop hxi mult f hf
  have hc := hcount top B xi 1 U hw htop hxi hxi1 hcomp (by norm_num) z (descendingWord f)
    hs hstart hallowed hK hlen hsource
  rw [word_search_count_eq_occupied hw htop hxi mult f hf hsingle] at hc
  refine ⟨hc,?_⟩
  have hl : ((descendingWord f).length:ℝ)=∑ b,(mult b:ℝ) := by
    exact_mod_cast global_word_length hw htop hxi mult f hf
  rwa [← hl]
end NumberTheoryLean.SafeAnchorSearchCount



namespace NumberTheoryLean.HardTagWordFamily
open HardTagBoxMass FiniteBoxWordMass ErdosCofactorChoices ErdosSubsetWord
open LogarithmicBinScale LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

attribute [local instance] Classical.propDecidable

private theorem finite_union_mass_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (M : Finset β) (T : β → Finset α) (W : α → ℝ) (hW : ∀ x,0 ≤ W x) :
    (∑ x ∈ M.biUnion T,W x) ≤ ∑ b ∈ M,∑ x ∈ T b,W x := by
  induction M using Finset.induction_on with
  | empty => simp
  | @insert b M hb ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert hb]
    have he : (∑ x ∈ T b ∪ M.biUnion T,W x)+(∑ x ∈ T b ∩ M.biUnion T,W x)=
        (∑ x ∈ T b,W x)+(∑ x ∈ M.biUnion T,W x) := Finset.sum_union_inter
    have hn : 0 ≤ ∑ x ∈ T b ∩ M.biUnion T,W x := Finset.sum_nonneg (fun x _ => hW x)
    linarith

noncomputable def hardBadWords {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) : Finset (List ℕ) :=
  (hardBadSelections (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q).image descendingWord

theorem hardBadWords_mass {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) :
    (∑ ps ∈ hardBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q,prefixWeight ps)=
      hardBadMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q := by
  have hd : Pairwise (fun i j => Disjoint (globalBins w top xi i) (globalBins w top xi j)) :=
    fun i j hij => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi i j hij
  rw [hardBadWords,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro f hf
    have hs := (Finset.mem_filter.mp hf).1
    rw [StoppedVertexHistory.prefixWeight_product,descendingWord_product (globalBins w top xi) hd f
      (fun i => ((mem_selections _ mult f).mp hs i).1)]
  · intro f hf g hg he
    exact word_injective (globalBins w top xi) hd f g
      (fun i => ((mem_selections _ mult f).mp (Finset.mem_filter.mp hf).1 i).1)
      (fun i => ((mem_selections _ mult g).mp (Finset.mem_filter.mp hg).1 i).1) he

noncomputable def hardWordFamily {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (M : Finset (Fin (binCount w top xi) → ℕ)) (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (a : ℕ → ℤ) : Finset (List ℕ) :=
  M.biUnion (fun mult => (Q mult).biUnion (fun q => hardBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q))

theorem hardWordFamily_mass_le {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (M : Finset (Fin (binCount w top xi) → ℕ)) (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (a : ℕ → ℤ) :
    (∑ ps ∈ hardWordFamily (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi M Q a,prefixWeight ps) ≤
      ∑ mult ∈ M,∑ q ∈ Q mult,hardBadMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q := by
  apply (finite_union_mass_le M _ prefixWeight prefixWeight_nonneg).trans
  apply Finset.sum_le_sum
  intro mult _hm
  have hh := finite_union_mass_le (Q mult)
    (fun q => hardBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q) prefixWeight prefixWeight_nonneg
  simpa only [hardBadWords_mass] using hh
end NumberTheoryLean.HardTagWordFamily



namespace NumberTheoryLean.SafeBoxTagRate
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
open SafeSubsetBoxGeometry SafeAnchorSearchCount SubsetTagFailureMass CanonicalSubsetBox
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinMaps
open CorrectSearchTags UniformSearchOwner ActualBinOwners ActualSourceTags
open ErdosCofactorChoices ErdosSubsetWord ErdosTagEvent ErdosSearchCount
open ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem safe_box_tag_rate {K Clen Cs eta xi : ℝ} (hC : 0 ≤ Clen) (hCs : 0 ≤ Cs)
    (heta0 : 0 < eta) (heta : eta < 1/2) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ w : ℝ in atTop,∀ (B top : ℝ) (hw : 1 < w) (htop : w < top),3 ≤ B →
      Real.log B ≤ 2*Real.log w → ∀ Y : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) → ∀ z : Node,
      z.side=.even → 199/100 ≤ z.ratio → Consistent z → z.cutoff=B → z.closed=true → w^B=top → w ≤ z.gap →
      ∀ mult : Fin (binCount w top xi) → ℕ,SafeAnchor hw htop hxi Clen B K z mult →
      (∀ b ∈ occupiedSearch w top xi mult,mult b=1) → ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      badMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q ≤
        (w^(-(searchConstant*eta/2))+w^(-1:ℝ))*selectionMass (globalBins w top xi) mult := by
  have htheta : 0 < xi/4 := by positivity
  have hwrong := canonical_wrong_mass (Cs := Cs) (theta := xi/4) (A := 1) (Clen := Clen)
    hCs htheta (by norm_num) hC
  filter_upwards [safe_anchor_search_count K Clen hC,uniform_correct_owner hCs heta htheta,hwrong] with w hcount howner hwrong
  intro B top hw htop hB hcomp Y hY hYup z hi h199 hz hcut hclosed hcap hstart mult hanchor hsingle a q hq
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hspan : (1+xi)*w ≤ top := by
    have hp : w^3 ≤ top := by
      have hh := Real.rpow_le_rpow_of_exponent_le hw.le hB
      rw [hcap] at hh
      simpa only [Real.rpow_ofNat] using hh
    have hw2 : 2 ≤ w := howner.1
    have hm := mul_nonneg hw0.le (show 0 ≤ w^2-2 by nlinarith)
    nlinarith
  have hwidth := common_width_bounds hw0 htop hxi hxi1 hspan
  have hvalid : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hstrong := source_strong_state hB z hi h199 hz hcut
  have hcounts := hcount top B xi hw htop hxi hxi1 hcomp z hvalid hz hstrong hclosed
    (by rwa [hcut]) hstart mult hanchor hsingle
  let I := occupiedSearch w top xi mult
  let R := lower w top xi
  have hidentify : ∀ b ∈ I,nearFull eta (R b) (width w top xi b) a q →
      owner Y w Cs eta (R b) (width w top xi b) a=some q := by
    intro b hb hnear
    exact howner.2 Y (R b) (width w top xi b) hY hYup (endpoint_pos hw0 _)
      (Finset.mem_filter.mp hb).2.1 hwidth.2.1 (hwidth.2.2.1.trans hxi1) a q hq hnear
  have hwm := hwrong Y (effectiveWidth w top xi) eta B hY hYup hwidth.2.1
    (hwidth.2.2.1.trans hxi1) hcomp (binCount w top xi) R mult hcounts.2 I hsingle
    (fun b hb => searchBin_lower hw (endpoint_pos hw0 _) (Finset.mem_filter.mp hb).2.1) a q hq
  have hmass : 0 ≤ selectionMass (globalBins w top xi) mult :=
    Finset.sum_nonneg (fun f _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  by_cases hnone : ∀ b ∈ I,¬nearFull eta (R b) (width w top xi b) a q
  · have hno := canonical_no_nearfull_mass R w searchConstant (effectiveWidth w top xi) eta mult
      (fun b => endpoint_pos hw0 _) hw searchConstant_pos hwidth.1.le (hwidth.2.2.1.trans hxi1)
      heta0 (by linarith) I hsingle hcounts.1 a q (fun b hb => (nonnearfull_card_lt _ _ _ _ _ (hnone b hb)).le)
    have hh := (bad_mass_le_alignment (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q).trans hno
    exact hh.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (Real.rpow_nonneg hw0.le (-1))) hmass)
  · push Not at hnone
    have hh := (bad_mass_le_wrong (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q hidentify hnone).trans hwm
    exact hh.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (Real.rpow_nonneg hw0.le (-(searchConstant*eta/2)))) hmass)
end NumberTheoryLean.SafeBoxTagRate



namespace NumberTheoryLean.RegularBadTagWords
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualWordSelection ActualRegularBoxes
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosSubsetWord ErdosCofactorChoices HardTagWordFamily HardTagBoxMass ActualSourceTags
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def badWordTest {Y w top xi Cs eta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (a : ℕ → ℤ) (ps : List ℕ) : Prop :=
    ∃ q ∈ Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),
      (∀ p ∈ ps,Cs < primeExponent w p → aligns a q p) ∧
      ¬∃ t,sourceTag Y w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a ps=some t ∧ t.rational=q

noncomputable def regularBadWords {Y w top xi Cs eta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Clen B K : ℝ) (z : Node)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (a : ℕ → ℤ) : Finset (List ℕ) :=
  (regularWords hw htop hxi Clen B K z).filter (badWordTest (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Q a)

theorem regularBadWords_subset {Y w top xi Cs eta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Clen B K : ℝ) (z : Node)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (a : ℕ → ℤ) :
    regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q a ⊆
      hardWordFamily (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi
        (regularBoxes hw htop hxi Clen B K z) Q a := by
  intro ps hp
  obtain ⟨hr,q,hq,ha,hbad⟩ := Finset.mem_filter.mp hp
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hr).1
  let lab := label (zero_lt_one.trans hw) htop hxi
  have hrec := wordSelection_recovers lab ps hd.1
  apply Finset.mem_biUnion.mpr
  refine ⟨wordMultiplicity lab ps,Finset.mem_image.mpr ⟨ps,hr,rfl⟩,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨q,hq,Finset.mem_image.mpr ⟨wordSelection lab ps,?_,hrec⟩⟩
  apply Finset.mem_filter.mpr
  refine ⟨wordSelection_mem hw htop hxi ps hd.2,?_⟩
  simpa only [hrec] using (show (∀ p ∈ ps,Cs < primeExponent w p → aligns a q p) ∧
    ¬∃ t,sourceTag Y w Cs eta (lower w top xi) (width w top xi) lab a ps=some t ∧ t.rational=q from ⟨ha,hbad⟩)

theorem regularBadWords_mass_le {Y w top xi Cs eta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Clen B K : ℝ) (z : Node)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (a : ℕ → ℤ) :
    (∑ ps ∈ regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q a,prefixWeight ps) ≤
      ∑ ps ∈ hardWordFamily (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi
        (regularBoxes hw htop hxi Clen B K z) Q a,prefixWeight ps :=
  Finset.sum_le_sum_of_subset_of_nonneg (regularBadWords_subset hw htop hxi Clen B K z Q a)
    (fun ps _ _ => prefixWeight_nonneg ps)
end NumberTheoryLean.RegularBadTagWords



namespace NumberTheoryLean.GlobalSafeTagCapture
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open SafeSubsetBoxGeometry SafeBoxTagRate ActualSafeBoxMass SubsetTagFailureMass CanonicalSubsetBox
open LogarithmicBinScale ActualBinOwners ErdosSubsetWord ErdosSearchCount

attribute [local instance] Classical.propDecidable

private theorem finite_candidate_sum {β : Type*} (M : Finset β) (Q : β → Finset ℚ)
    (H : ℕ) (r : ℝ) (hr : 0 ≤ r) (F : β → ℝ) (hF : ∀ b ∈ M,0 ≤ F b)
    (G : β → ℚ → ℝ) (hG : ∀ b ∈ M,∀ q ∈ Q b,G b q ≤ r*F b)
    (hQ : ∀ b ∈ M,(Q b).card ≤ H) :
    (∑ b ∈ M,∑ q ∈ Q b,G b q) ≤ (H:ℝ)*r*(∑ b ∈ M,F b) := by
  calc
    _ ≤ ∑ b ∈ M,∑ _q ∈ Q b,r*F b := Finset.sum_le_sum (fun b hb => Finset.sum_le_sum (fun q hq => hG b hb q hq))
    _ = ∑ b ∈ M,((Q b).card:ℝ)*(r*F b) := by simp
    _ ≤ ∑ b ∈ M,(H:ℝ)*(r*F b) := Finset.sum_le_sum (fun b hb =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast hQ b hb) (mul_nonneg hr (hF b hb)))
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring

theorem global_bad_tag_mass_small {K Clen Cs eta xi : ℝ} (hK : 3 ≤ K) (hC : 0 ≤ Clen) (hCs : 0 ≤ Cs)
    (heta0 : 0 < eta) (heta : eta < 1/2) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hDelta : 2*Clen*xi ≤ 1) (H : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ B₀ w₀ : ℝ,3 ≤ B₀ ∧ 1 < w₀ ∧ ∀ (B w top : ℝ) (hw : 1 < w) (htop : w < top),
      B₀ ≤ B → w₀ ≤ w → Real.log B ≤ 2*Real.log w → ∀ Y : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) →
      ∀ (z : Node) (a : ℕ → ℤ),z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 →
      Consistent z → z.cutoff=B → z.closed=true → w^B=top → w ≤ z.gap →
      ∀ (M : Finset (Fin (binCount w top xi) → ℕ)) (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ),
      (∀ mult ∈ M,SafeAnchor hw htop hxi Clen B K z mult) →
      (∀ mult ∈ M,∀ b ∈ occupiedSearch w top xi mult,mult b=1) →
      (∀ mult ∈ M,(Q mult).card ≤ H) → (∀ mult ∈ M,∀ q ∈ Q mult,eligible Y w Cs q) →
      B^2*(∑ mult ∈ M,∑ q ∈ Q mult,badMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q) ≤ epsilon := by
  obtain ⟨C,B₀,wbox,hCpos,hB₀,hwbox,hboxes⟩ := uniform_safe_box_mass K hK
  have hd : 0 < searchConstant*eta/2 := by have hc := searchConstant_pos; positivity
  have hrate : Tendsto (fun w : ℝ => (H:ℝ)*C*(w^(-(searchConstant*eta/2))+w^(-1:ℝ))) atTop (nhds 0) := by
    have hh := ((tendsto_rpow_neg_atTop hd).add (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1))).const_mul ((H:ℝ)*C)
    simpa only [zero_add,mul_zero] using hh
  have hsmall : ∀ᶠ w : ℝ in atTop,(H:ℝ)*C*(w^(-(searchConstant*eta/2))+w^(-1:ℝ)) ≤ epsilon :=
    ((tendsto_order.mp hrate).2 epsilon hepsilon).mono (fun _ h => h.le)
  have htag := safe_box_tag_rate (K := K) (Clen := Clen) (Cs := Cs) (eta := eta) (xi := xi) hC hCs heta0 heta hxi hxi1
  obtain ⟨w₁,hw₁⟩ := eventually_atTop.mp (htag.and (hsmall.and (eventually_ge_atTop wbox)))
  refine ⟨B₀,max 2 w₁,hB₀,by have hh := le_max_left (2:ℝ) w₁; linarith,?_⟩
  intro B w top hw htop hB hW hcomp Y hY hYup z a hi h199 h23 hz hcut hclosed hcap hstart M Q hanchor hsingle hcard helig
  have hgood := hw₁ w ((le_max_right _ _).trans hW)
  have hB3 := hB₀.trans hB
  let r := w^(-(searchConstant*eta/2))+w^(-1:ℝ)
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hr : 0 ≤ r := add_nonneg (Real.rpow_nonneg hw0.le _) (Real.rpow_nonneg hw0.le _)
  have hm := finite_candidate_sum M Q H r hr (selectionMass (globalBins w top xi))
    (fun mult _ => Finset.sum_nonneg (fun f _ => inv_nonneg.mpr (Nat.cast_nonneg _)))
    (fun mult q => badMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q)
    (fun mult hmult q hq => hgood.1 B top hw htop hB3 hcomp Y hY hYup z hi h199 hz hcut hclosed hcap hstart
      mult (hanchor mult hmult) (hsingle mult hmult) a q (helig mult hmult q hq)) hcard
  have hbox := hboxes B w top hB hgood.2.2 hw htop xi Clen hxi hC hcomp hDelta z hi h199 h23 hz hcut hclosed hcap M hanchor
  calc
    _ ≤ B^2*((H:ℝ)*r*(∑ mult ∈ M,selectionMass (globalBins w top xi) mult)) := mul_le_mul_of_nonneg_left hm (sq_nonneg B)
    _ = (H:ℝ)*r*(B^2*(∑ mult ∈ M,selectionMass (globalBins w top xi) mult)) := by ring
    _ ≤ (H:ℝ)*r*C := mul_le_mul_of_nonneg_left hbox (mul_nonneg (Nat.cast_nonneg _) hr)
    _ = (H:ℝ)*C*r := by ring
    _ ≤ epsilon := hgood.2.1
end NumberTheoryLean.GlobalSafeTagCapture



namespace NumberTheoryLean.PaperSafeTagCapture
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership SourceNodeCoordinates
open JacobsthalSourceScale PaperMissingPrimeWindow PaperOwnerHeight PaperBinOwners
open SafeSubsetBoxGeometry GlobalSafeTagCapture HardTagBoxMass ActualBinOwners
open LogarithmicBinScale ErdosSubsetWord

attribute [local instance] Classical.propDecidable

theorem paper_safe_hard_tag_capture {K Clen Cs eta xi : ℝ} (hK : 3 ≤ K) (hC : 0 ≤ Clen) (hCs : 0 ≤ Cs)
    (heta0 : 0 < eta) (heta : eta < 1/2) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hDelta : 2*Clen*xi ≤ 1) (H : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      ∀ Y : ℕ,Y ≤ ⌊top^2/(Real.log top)^2⌋₊ → ∀ (z : Node) (a : ℕ → ℤ),
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=sourceB (Real.log top) → z.closed=true →
      ∀ (M : Finset (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ))
        (Q : (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ) → Finset ℚ),
      (∀ mult ∈ M,SafeAnchor hw htop hxi Clen (sourceB (Real.log top)) K z mult) →
      (∀ mult ∈ M,∀ b ∈ occupiedSearch (sourceW (Real.log top)) top xi mult,mult b=1) →
      (∀ mult ∈ M,(Q mult).card ≤ H) →
      (∀ mult ∈ M,∀ q ∈ Q mult,eligible Y (sourceW (Real.log top)) Cs q) →
      (sourceB (Real.log top))^2 *
        (∑ mult ∈ M,∑ q ∈ Q mult,hardBadMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q) ≤ epsilon := by
  obtain ⟨B₀,w₀,_hB₀,_hw₀,hbound⟩ := global_bad_tag_mass_small hK hC hCs heta0 heta hxi hxi1 hDelta H epsilon hepsilon
  have hwT := sourceW_tendsto.comp Real.tendsto_log_atTop
  have hBT := sourceB_tendsto.comp Real.tendsto_log_atTop
  have hsearch : ∀ᶠ top : ℝ in atTop,Cs ≤ (sourceW (Real.log top))^((1/4:ℝ)) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp hwT).eventually_ge_atTop Cs
  filter_upwards [paper_bin_span hxi hxi1,Real.tendsto_log_atTop.eventually source_scale_eventually,
    Real.tendsto_log_atTop.eventually sourceW_le_sourceB_eventually,literal_source_floor_height,
    hwT.eventually_ge_atTop w₀,hBT.eventually_ge_atTop B₀,eventually_gt_atTop (1:ℝ),hsearch]
    with top hspan hscale hWB hheight hwBound hBBound htop1 hsearch
  have hw : 1 < sourceW (Real.log top) := by linarith [hspan.1]
  refine ⟨hw,hspan.2.1,?_⟩
  intro Y hY z a hi h199 h23 hz hcut hclosed M Q hanchors hsingle hcard helig
  have hYup : (Y:ℝ) ≤ Real.exp ((sourceW (Real.log top))^2) :=
    (show (Y:ℝ) ≤ (⌊top^2/(Real.log top)^2⌋₊:ℕ) by exact_mod_cast hY).trans hheight
  have hcap : (sourceW (Real.log top))^(sourceB (Real.log top))=top :=
    (sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans htop1))
  have hgap := (source_node_bounds hscale.2.1 z hi h199 h23 hz hcut).2.2.1
  have hstart := hWB.trans hgap
  have hh := hbound (sourceB (Real.log top)) (sourceW (Real.log top)) top hw hspan.2.1 hBBound hwBound
    hscale.2.2.2.2 Y (Nat.cast_nonneg Y) hYup z a hi h199 h23 hz hcut hclosed hcap hstart M Q hanchors hsingle hcard helig
  apply le_trans _ hh
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro mult _hm
  apply Finset.sum_le_sum
  intro q _hq
  exact hardBadMass_le_badMass hw hspan.2.1 hxi hsearch mult a q
end NumberTheoryLean.PaperSafeTagCapture



namespace NumberTheoryLean.PaperSafeWordCapture
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open JacobsthalSourceScale SafeSubsetBoxGeometry HardTagWordFamily ActualBinOwners
open LogarithmicBinScale ErdosSubsetWord PaperSafeTagCapture

attribute [local instance] Classical.propDecidable

theorem paper_safe_hard_word_capture {K Clen Cs eta xi : ℝ} (hK : 3 ≤ K) (hC : 0 ≤ Clen) (hCs : 0 ≤ Cs)
    (heta0 : 0 < eta) (heta : eta < 1/2) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hDelta : 2*Clen*xi ≤ 1) (H : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      ∀ Y : ℕ,Y ≤ ⌊top^2/(Real.log top)^2⌋₊ → ∀ (z : Node) (a : ℕ → ℤ),
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=sourceB (Real.log top) → z.closed=true →
      ∀ (M : Finset (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ))
        (Q : (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ) → Finset ℚ),
      (∀ mult ∈ M,SafeAnchor hw htop hxi Clen (sourceB (Real.log top)) K z mult) →
      (∀ mult ∈ M,∀ b ∈ occupiedSearch (sourceW (Real.log top)) top xi mult,mult b=1) →
      (∀ mult ∈ M,(Q mult).card ≤ H) →
      (∀ mult ∈ M,∀ q ∈ Q mult,eligible Y (sourceW (Real.log top)) Cs q) →
      (sourceB (Real.log top))^2 *
        (∑ ps ∈ hardWordFamily (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi M Q a,ErdosPrimeInputs.PrimePrefixMass.prefixWeight ps) ≤ epsilon := by
  filter_upwards [paper_safe_hard_tag_capture hK hC hCs heta0 heta hxi hxi1 hDelta H epsilon hepsilon] with top htopData
  obtain ⟨hw,htop,hbound⟩ := htopData
  refine ⟨hw,htop,?_⟩
  intro Y hY z a hi h199 h23 hz hcut hclosed M Q hanchors hsingle hcard helig
  have hh := hbound Y hY z a hi h199 h23 hz hcut hclosed M Q hanchors hsingle hcard helig
  exact (mul_le_mul_of_nonneg_left (hardWordFamily_mass_le (Y := Y) (Cs := Cs) (eta := eta)
    hw htop hxi M Q a) (sq_nonneg (sourceB (Real.log top)))).trans hh
end NumberTheoryLean.PaperSafeWordCapture



namespace NumberTheoryLean.PaperRegularTagCapture
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open JacobsthalSourceScale ActualRegularBoxes ActualPrefixClearance RegularBadTagWords
open PaperSafeWordCapture ActualBinOwners LogarithmicBinScale

attribute [local instance] Classical.propDecidable

theorem paper_regular_bad_tag_mass {K Clen Cs eta xi : ℝ} (hK : 3 ≤ K) (hC : 1 ≤ Clen) (hCs : 0 ≤ Cs)
    (heta0 : 0 < eta) (heta : eta < 1/2) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hDelta : 2*Clen*xi ≤ 1) (H : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      ∀ Y : ℕ,Y ≤ ⌊top^2/(Real.log top)^2⌋₊ → ∀ (z : Node) (a : ℕ → ℤ),
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=sourceB (Real.log top) → z.closed=true →
      ∀ Q : (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ) → Finset ℚ,
      (∀ mult ∈ regularBoxes hw htop hxi Clen (sourceB (Real.log top)) K z,(Q mult).card ≤ H) →
      (∀ mult ∈ regularBoxes hw htop hxi Clen (sourceB (Real.log top)) K z,
        ∀ q ∈ Q mult,eligible Y (sourceW (Real.log top)) Cs q) →
      (sourceB (Real.log top))^2 *
        (∑ ps ∈ regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen
          (sourceB (Real.log top)) K z Q a,ErdosPrimeInputs.PrimePrefixMass.prefixWeight ps) ≤ epsilon := by
  have hC0 : 0 ≤ Clen := by linarith
  have hwT := sourceW_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [paper_safe_hard_word_capture hK hC0 hCs heta0 heta hxi hxi1 hDelta H epsilon hepsilon,
    Real.tendsto_log_atTop.eventually source_scale_eventually,
    (Real.tendsto_log_atTop.comp hwT).eventually_ge_atTop 1] with top hbound hscale hlog
  obtain ⟨hw,htop,hbound⟩ := hbound
  refine ⟨hw,htop,?_⟩
  intro Y hY z a hi h199 h23 hz hcut hclosed Q hcard helig
  have hsmall := source_mesh_clearance_condition hlog hxi.le hC
  have hh := hbound Y hY z a hi h199 h23 hz hcut hclosed
    (regularBoxes hw htop hxi Clen (sourceB (Real.log top)) K z) Q
    (regular_boxes_anchors hw htop hxi hC0 hscale.2.2.2.2 hsmall z)
    (regular_boxes_search_singletons hw htop hxi z) hcard helig
  exact (mul_le_mul_of_nonneg_left (regularBadWords_mass_le (Y := Y) (Cs := Cs) (eta := eta)
    hw htop hxi Clen (sourceB (Real.log top)) K z Q a) (sq_nonneg _)).trans hh
end NumberTheoryLean.PaperRegularTagCapture



namespace NumberTheoryLean.FullWordHighAlignment
open ErdosSubsetWord ErdosCofactorChoices ErdosInverseAlignment
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinEndpoints
open ParentTailPartition ParentCofactorChoices BinCutSelections SingletonBinSelection
open TwoPrimeObservableSum BoundedEdgeBins BoundedEdgeHighPrimes
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem parent_prime_factors {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (i j : Fin (binCount w top xi)) :
    (selectionProduct (parentCofactorSelection f i j)).primeFactors=
      selectionPrimes (parentCofactorSelection f i j) := by
  have hc := erase_selection_mem _ _ _ (above_selection_mem _ m f hf j) i
  exact selectionProduct_primeFactors (globalBins w top xi)
    (fun k _p hp => (bin_prime_in_source (zero_lt_one.trans hw) htop hxi k hp).1)
    (fun k l hkl => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl)
    (parentCofactorSelection f i j) (fun k => ((mem_selections _ _ _).mp hc k).1)

theorem full_word_high_alignment {w top xi Cs M X : ℝ} {Y : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hCs : X+xi/Real.log w ≤ Cs)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (i j : Fin (binCount w top xi))
    (hi : m i=1) (hj : boundedEdgeBin w top xi Y m M X j)
    (a : ℕ → ℤ) (q : ℚ) (hiso : aligns a q (pickedPrime f i))
    (hparent : ∀ p∈(selectionProduct (parentCofactorSelection f i j)).primeFactors,
      Cs < primeExponent w p → aligns a q p) :
    ∀ p∈descendingWord f,Cs < primeExponent w p → aligns a q p := by
  intro p hp hhigh
  obtain ⟨k,hpk⟩ := (mem_descendingWord f p).mp hp
  by_cases hki : k=i
  · subst k
    obtain ⟨p0,_hp0,hfi,_hfill⟩ := singleton_selection_recovery _ m i hi f hf
    have he : p=p0 := by simpa only [hfi,Finset.mem_singleton] using hpk
    simpa [pickedPrime,hfi,he] using hiso
  · have hjk : j < k := by
      by_contra! hkj
      have hpbin := ((mem_selections _ _ _).mp hf k).1 hpk
      exact (not_le_of_gt hhigh) ((bounded_edge_descendant_exponent hw htop hxi m j k hj hkj hpbin).trans hCs)
    apply hparent p _ hhigh
    rw [parent_prime_factors hw htop hxi m f hf i j]
    apply Finset.mem_biUnion.mpr
    exact ⟨k,Finset.mem_univ _,by simpa [parentCofactorSelection,eraseSelection,aboveSelection,hki,hjk] using hpk⟩

theorem full_word_high_alignment_fixed_cutoff {w top xi Cs M X : ℝ} {Y : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hlog : 1 ≤ Real.log w) (hxi1 : xi ≤ 1) (hCs : X+1 ≤ Cs)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (i j : Fin (binCount w top xi))
    (hi : m i=1) (hj : boundedEdgeBin w top xi Y m M X j)
    (a : ℕ → ℤ) (q : ℚ) (hiso : aligns a q (pickedPrime f i))
    (hparent : ∀ p∈(selectionProduct (parentCofactorSelection f i j)).primeFactors,
      Cs < primeExponent w p → aligns a q p) :
    ∀ p∈descendingWord f,Cs < primeExponent w p → aligns a q p := by
  apply full_word_high_alignment hw htop hxi _ m f hf i j hi hj a q hiso hparent
  have hh : xi/Real.log w ≤ 1 := (div_le_one (Real.log_pos hw)).mpr (hxi1.trans hlog)
  linarith
end NumberTheoryLean.FullWordHighAlignment


end Erdos970

end OAI
