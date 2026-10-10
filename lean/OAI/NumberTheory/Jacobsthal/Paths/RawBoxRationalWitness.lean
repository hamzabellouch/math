import OAI.NumberTheory.Jacobsthal.Estimates.ParentProductReadout

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RecentCountWitness
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission ActualReferencePrefixes
open WordIntervalGeometry RecentReferenceSegment ActualCountErrorEdges FiniteErrorTelescoping SourcePrimeProductData
open LogarithmicBinPartition ErdosInverseCounts ErdosModulusRelative
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

theorem recent_count_witness (K eps : ℝ) (hK : 3 ≤ K) (heps : 0 < eps) :
    ∃ Kstar B₀ w₀ : ℝ,K+10 < Kstar ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
    ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ _hw : 1 < w,∀ _htop : w < top,
      ∀ aStar : ℝ,0 ≤ aStar → aStar ≤ 1 → ∀ Y : ℕ,0 < Y → ∀ z : Node,
      z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 → z.side=.even → 199/100 ≤ z.ratio →
      Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ residue : ℕ → ℕ,∀ ps : List ℕ,
      ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (terminal w z ps).gap ≤ K →
      eps < |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) ps| →
      ∃ before u after,ps=before++u::after ∧ (u::after).length ≤ ⌈2*Kstar+10⌉₊ ∧
        NodeBadEdge Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
          (eps/(4*(⌈2*Kstar+10⌉₊:ℝ))) (SmallSieveFinite.smallEuler ⌊w⌋₊) before.prod u ∧
        wordIntervalExponent w Y before ≤ 2*Kstar+3 ∧ aStar ≤ wordIntervalExponent w Y (before++[u]) ∧
        primeExponent w u ≤ 2*Kstar+3 ∧ (terminal w z before).gap ≤ 2*Kstar+5 := by
  obtain ⟨K0,W,hK0,hW,hSmall⟩ := uniform_modulus_small_relative (eps/2) (by positivity)
  let Kstar := max (K+11) K0
  have hKstar : K+10 < Kstar := (by linarith : K+10<K+11).trans_le (le_max_left _ _)
  have hK0star : K0 ≤ Kstar := le_max_right _ _
  refine ⟨Kstar,max 3 (2*(Kstar+2)),max W 2,hKstar,le_max_left _ _,hW.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ hw htop aStar ha0 ha1 Y hY z hroot hi h199 hz hcut hclosed hpower residue ps hps hend hbad
  have hB3 : 3 ≤ B := (le_max_left _ _).trans hB
  have hBlarge : 2*(Kstar+2-aStar) ≤ B := by
    have hh := (le_max_right _ _).trans hB
    linarith
  have hw2 : 2 ≤ w := (le_max_right _ _).trans hw₀
  have hV : 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    (inv_pos.mpr (zero_lt_one.trans hw)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  obtain ⟨pre,rest,hword,_hpre,_hrest,hhigh,hlen,hsegment⟩ := recent_reference_segment hw htop hK hKstar.le
    ha0 ha1 hB3 hBlarge Y hY z hroot hi h199 hz hcut hclosed hpower ps hps hend
  have hpreIn : pre ∈ ps.inits := (List.mem_inits _ _).mpr ⟨rest,hword.symm⟩
  have hpreRef := reference_prefix_mem w _ _ _ ps pre hps hpreIn
  have hpreData := reference_word_product_data hw htop z.side z.gap pre hpreRef
  have hstart := hSmall w ((le_max_left _ _).trans hw₀) Y pre.prod residue hY hpreData.1 hpreData.2.1 hpreData.2.2
    (hK0star.trans hhigh.le)
  change |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) pre| ≤ eps/2 at hstart
  have hH : 0 < ⌈2*Kstar+10⌉₊ := by
    have hh := Nat.le_ceil (2*Kstar+10)
    by_contra! hn
    have he : ⌈2*Kstar+10⌉₊=0 := by omega
    rw [he,Nat.cast_zero] at hh
    linarith
  obtain ⟨mid,u,after,hrest,hedge⟩ := witness_from_endpoints
    (wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊))
    pre rest ⌈2*Kstar+10⌉₊ hH eps heps hlen hstart (by rwa [← hword])
  have hfull : ps=(pre++mid)++u::after := by rw [hword,hrest,List.append_assoc]
  have hbeforeIn : pre++mid ∈ ps.inits := (List.mem_inits _ _).mpr ⟨u::after,hfull.symm⟩
  have hbeforeRef := reference_prefix_mem w _ _ _ ps _ hps hbeforeIn
  have hbeforeData := reference_word_product_data hw htop z.side z.gap _ hbeforeRef
  have huMem : u ∈ ps := by rw [hfull]; simp
  have huPos : 0 < u := ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop u).mp
    ((ErdosPrimeInputs.PrimePrefixMass.mem_decreasingPrefixes.mp (Finset.mem_filter.mp hps).1).2 u huMem)).1.pos
  have hEdge := (word_large_edge_iff Y _ residue (SmallSieveFinite.smallEuler ⌊w⌋₊) (eps/(4*(⌈2*Kstar+10⌉₊:ℝ)))
    hY hV (pre++mid) u hbeforeData.1 huPos).mp hedge
  refine ⟨pre++mid,u,after,hfull,?_,hEdge,hsegment mid u after hrest⟩
  have hh : (u::after).length ≤ rest.length := by rw [hrest,List.length_append]; omega
  exact hh.trans hlen
end NumberTheoryLean.RecentCountWitness



namespace NumberTheoryLean.CountWitnessReadout
open PrimeHistories ErdosCofactorChoices ErdosSubsetWord ErdosInverseCounts
open ParentProductReadout TwoPrimeObservableSum ParentTailPartition
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition


theorem selected_edge_singleton {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) (hj : m j=1)
    (u : ℕ) (hu : u ∈ descendingWord f) (hlab : label (zero_lt_one.trans hw) htop hxi u=j) : f j={u} := by
  obtain ⟨k,huk⟩ := (mem_descendingWord f u).mp hu
  have hk : j=k := hlab.symm.trans (selected_prime_label hw htop hxi m f hf k huk)
  have huj : u ∈ f j := by rwa [hk]
  obtain ⟨v,hfv⟩ := Finset.card_eq_one.mp (((mem_selections _ _ _).mp hf j).2.trans hj)
  have huv : u=v := by simpa only [hfv,Finset.mem_singleton] using huj
  rwa [← huv] at hfv

theorem observed_node_bad_edge {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (i j : Fin (binCount w top xi))
    (hji : j < i) (hi : m i=1) (hj : m j=1) (pre tail : List ℕ) (u : ℕ)
    (he : descendingWord f=pre++u::tail) (hlab : label (zero_lt_one.trans hw) htop hxi u=j)
    (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ)
    (hbad : NodeBadEdge Y small a delta V0 pre.prod u) :
    WitnessingBadEdge Y small a delta V0 (pickedPrime f i)
      (selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j) := by
  have hu : u ∈ descendingWord f := by rw [he]; simp
  have hfu := selected_edge_singleton hw htop hxi m f hf j hj u hu hlab
  have hread := actual_prefix_product_readout hw htop hxi m f hf i j hji hi pre tail u he hfu
  unfold WitnessingBadEdge
  rw [hread.2,← hread.1]
  exact hbad
end NumberTheoryLean.CountWitnessReadout



namespace NumberTheoryLean.GeometricRecentWitness
open FinitePathGeometry PrimeHistories PrimeBinMembership RecentCountWitness ActualCountErrorEdges
open GeometricRegularWords GeometricEdgeWitness ActualWordSelection ActualRegularAdmission BoundedEdgeBins
open CountWitnessReadout TwoPrimeObservableSum ParentTailPartition
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseCounts
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem geometric_recent_witness (K eps : ℝ) (hK : 3 ≤ K) (heps : 0 < eps) :
    ∃ Kstar B₀ w₀ : ℝ,K+10 < Kstar ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
    ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ hw : 1 < w,∀ htop : w < top,
      ∀ xi : ℝ,∀ hxi : 0 < xi,∀ C : ℝ,1 ≤ C → Real.log B ≤ 2*Real.log w →
      ∀ aStar alpha beta : ℝ,0 ≤ aStar → aStar ≤ 1 → ∀ Y : ℕ,0 < Y → ∀ z : Node,
      z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 → z.side=.even → 199/100 ≤ z.ratio →
      Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ residue : ℕ → ℕ,∀ ps : List ℕ,
      ps ∈ geometricWords hw htop hxi C B K (2*Kstar+5) alpha beta z →
      eps < |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) ps| →
      let m := wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps
      let f := wordSelection (label (zero_lt_one.trans hw) htop hxi) ps
      ∃ j : Fin (binCount w top xi),boundedEdgeBin w top xi Y m (2*Kstar+3) (2*Kstar+3) j ∧
        ∀ i : Fin (binCount w top xi),m i=1 → j < i →
        WitnessingBadEdge Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
          (eps/(4*(⌈2*Kstar+10⌉₊:ℝ))) (SmallSieveFinite.smallEuler ⌊w⌋₊)
          (pickedPrime f i) (selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j) := by
  obtain ⟨Kstar,B₀,W,hKs,hB₀,hW,hWitness⟩ := recent_count_witness K eps hK heps
  refine ⟨Kstar,B₀,max W (Real.exp 1),hKs,hB₀,hW.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ hw htop xi hxi C hC hcomp aStar alpha beta ha0 ha1 Y hY z hroot hi h199 hz hcut hclosed hpower residue ps hps hbad
  have hlog : 1 ≤ Real.log w := by
    have hh := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hw₀)
    simpa only [Real.log_exp] using hh
  have hsmall : 2*(xi/Real.log w) ≤ 6*(2*C*xi) := by
    have hh := div_le_self hxi.le hlog
    nlinarith
  have hreg := (Finset.mem_filter.mp hps).1
  have hRef := regular_word_reference hw htop hxi (by linarith : 0 ≤ C) hcomp hsmall z ps hreg
  have hgap := (Finset.mem_filter.mp hreg).2.2.2.1
  obtain ⟨pre,u,tail,he,_hlen,hNode,hM,_hchild,hX,hparent⟩ := hWitness B w top hB ((le_max_left _ _).trans hw₀) hw htop
    aStar ha0 ha1 Y hY z hroot hi h199 hz hcut hclosed hpower residue ps hRef hgap hbad
  dsimp only
  let lab := label (zero_lt_one.trans hw) htop hxi
  let m := wordMultiplicity lab ps
  let f := wordSelection lab ps
  let j := lab u
  have hCandidate := geometric_word_bounded_edge hw htop hxi Y z ps hps pre tail u he hparent hM hX
  refine ⟨j,hCandidate,?_⟩
  intro i hmi hji
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hreg).1
  have hf : f ∈ selections (globalBins w top xi) m := wordSelection_mem hw htop hxi ps hd.2
  have hword : descendingWord f=ps := wordSelection_recovers lab ps hd.1
  exact observed_node_bad_edge hw htop hxi m f hf i j hji hmi (bounded_edge_singleton m j hCandidate)
    pre tail u (hword.trans he) rfl Y _ residue _ _ hNode
end NumberTheoryLean.GeometricRecentWitness



namespace NumberTheoryLean.StructuredWitnessOutside
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseCounts ErdosInverseBoxApplication ErdosInverseSampleCost
open ErdosInverseAlignment ErdosInverseStructured ErdosPrimitiveIntercept
open PrimeHistories TwoPrimeObservableSum ParentTailPartition ParentCofactorChoices SingletonBinSelection BinCutSelections
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

theorem full_selection_coordinates {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P m) (i j : Fin n) (hi : m i=1) (hj : m j=1) :
    pickedPrime f i ∈ P i ∧ pickedPrime f j ∈ P j ∧
      selectionProduct (parentCofactorSelection f i j) ∈ cofactorChoices P (parentCofactorMultiplicity m i j) := by
  obtain ⟨p,hp,hfi,_⟩ := singleton_selection_recovery P m i hi f hf
  obtain ⟨u,hu,hfj,_⟩ := singleton_selection_recovery P m j hj f hf
  refine ⟨by simpa [pickedPrime,hfi] using hp,by simpa [pickedPrime,hfj] using hu,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨parentCofactorSelection f i j,?_,rfl⟩
  exact erase_selection_mem P (aboveMultiplicity m j) (aboveSelection f j) (above_selection_mem P m f hf j) i

theorem structured_full_selection {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P m) (i j : Fin n) (hi : m i=1) (hj : m j=1)
    (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 S R Z cp sigma : ℝ) (F : ℕ)
    (hInv : SourceInverseConclusion Y small a delta V0 S R Z cp sigma F
      (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j))
    (hbad : WitnessingBadEdge Y small a delta V0 (pickedPrime f i)
      (selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j))
    (hout : ¬actualWitness Y small a delta V0 (P i) S R Z cp
      (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)) :
    ∃ t ∈ sourceRationalList (P i) (fun p => (a p:ℤ)) S R Z cp,
      aligns (fun p => (a p:ℤ)) t (pickedPrime f i) ∧
      ((t.den*badPrimeProduct (fun p => (a p:ℤ)) t (selectionProduct (parentCofactorSelection f i j)):ℕ):ℝ) ≤ R*Z^10 := by
  have hc := full_selection_coordinates P m f hf i j hi hj
  have hnot : ((pickedPrime f i,selectionProduct (parentCofactorSelection f i j)),pickedPrime f j) ∉
      actualInverseException Y small a delta V0 S R Z cp (P i)
        (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j) := by
    intro he
    have hh := (mem_actualInverseException Y small a delta V0 S R Z cp _ _ _ _ _ _).mp he
    exact hout ⟨hh.2.2.2.1,hh.2.2.2.2⟩
  exact hInv.2.2.2 _ hc.1 _ hc.2.2 _ hc.2.1 hnot hbad
end NumberTheoryLean.StructuredWitnessOutside



namespace NumberTheoryLean.RawBoxRationalWitness
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseCounts ErdosInverseBoxApplication ErdosInverseSampleCost
open ErdosInverseAlignment ErdosInverseStructured ErdosPrimitiveIntercept
open StructuredWitnessOutside TwoPrimeObservableSum ParentTailPartition ParentCofactorChoices

attribute [local instance] Classical.propDecidable

noncomputable def rawBoxList {n : ℕ} (P : Fin n → Finset ℕ) (i : Fin n) (J : Finset (Fin n))
    (a : ℕ → ℕ) (S : Fin n → ℝ) (R Z cp : ℝ) : Finset ℚ :=
  J.biUnion (fun j => sourceRationalList (P i) (fun p => (a p:ℤ)) (S j) R Z cp)

theorem raw_box_list_card {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (J : Finset (Fin n))
    (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ) (S : Fin n → ℝ) (R Z cp sigma : ℝ) (F : ℕ)
    (hInv : ∀ j∈J,SourceInverseConclusion Y small a delta V0 (S j) R Z cp sigma F
      (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j)) :
    (rawBoxList P i J a S R Z cp).card ≤ J.card*F := by
  have hh := (Finset.card_biUnion_le : (rawBoxList P i J a S R Z cp).card ≤
    ∑ j∈J,(sourceRationalList (P i) (fun p => (a p:ℤ)) (S j) R Z cp).card)
  exact hh.trans ((Finset.sum_le_sum (fun j hj => (hInv j hj).1)).trans_eq (by simp))

theorem raw_box_witness {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (J : Finset (Fin n))
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P m) (hi : m i=1) (hj : ∀ j∈J,m j=1)
    (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ) (S : Fin n → ℝ) (R Z cp sigma : ℝ) (F : ℕ)
    (hInv : ∀ j∈J,SourceInverseConclusion Y small a delta V0 (S j) R Z cp sigma F
      (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j))
    (hbad : ∃ j∈J,WitnessingBadEdge Y small a delta V0 (pickedPrime f i)
      (selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j))
    (hout : ¬∃ j∈J,actualWitness Y small a delta V0 (P i) (S j) R Z cp
      (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)) :
    ∃ j∈J,∃ t∈rawBoxList P i J a S R Z cp,
      t ∈ sourceRationalList (P i) (fun p => (a p:ℤ)) (S j) R Z cp ∧
      aligns (fun p => (a p:ℤ)) t (pickedPrime f i) ∧
      ((t.den*badPrimeProduct (fun p => (a p:ℤ)) t (selectionProduct (parentCofactorSelection f i j)):ℕ):ℝ) ≤ R*Z^10 := by
  obtain ⟨j,hjJ,hb⟩ := hbad
  have hno : ¬actualWitness Y small a delta V0 (P i) (S j) R Z cp
      (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j) :=
    fun h => hout ⟨j,hjJ,h⟩
  obtain ⟨t,ht,ha,hd⟩ := structured_full_selection P m f hf i j hi (hj j hjJ) Y small a delta V0 (S j) R Z cp sigma F
    (hInv j hjJ) hb hno
  exact ⟨j,hjJ,t,Finset.mem_biUnion.mpr ⟨j,hjJ,ht⟩,ht,ha,hd⟩
end NumberTheoryLean.RawBoxRationalWitness


end Erdos970

end OAI
