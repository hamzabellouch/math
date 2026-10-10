import OAI.NumberTheory.Jacobsthal.Estimates.EndpointSoftConclusion
import OAI.NumberTheory.Jacobsthal.Partitions.EligibleBoxLists

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FilteredBoxWordMass
open ErdosCofactorChoices ErdosSubsetWord FiniteBoxWordMass
open ErdosPrimeInputs.PrimePrefixMass
open GeometricBoxImages ExpandedCompactPartition GeometricRegularWords ActualWordSelection
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

noncomputable def selectedWordMass {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (F : Finset (List ℕ)) : ℝ :=
  ∑ f∈(selections P m).filter (fun f => descendingWord f∈F),(selectionProduct f:ℝ)⁻¹

theorem filtered_word_box_mass {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (F : Finset (List ℕ)) :
    (∑ ps∈(wordBox P m).filter (fun ps => ps∈F),prefixWeight ps)=selectedWordMass P m F := by
  have he : (wordBox P m).filter (fun ps => ps∈F)=
      ((selections P m).filter (fun f => descendingWord f∈F)).image descendingWord := by
    ext ps
    simp only [wordBox,Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨f,hf,rfl⟩,hF⟩
      exact ⟨f,⟨hf,hF⟩,rfl⟩
    · rintro ⟨f,⟨hf,hF⟩,rfl⟩
      exact ⟨⟨f,hf,rfl⟩,hF⟩
  rw [he,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro f hf
    rw [StoppedVertexHistory.prefixWeight_product,
      descendingWord_product P hd f (fun k => ((mem_selections _ _ _).mp (Finset.mem_filter.mp hf).1 k).1)]
  · intro f hf g hg heq
    exact word_injective P hd f g
      (fun k => ((mem_selections _ _ _).mp (Finset.mem_filter.mp hf).1 k).1)
      (fun k => ((mem_selections _ _ _).mp (Finset.mem_filter.mp hg).1 k).1) heq

theorem filtered_box_mass {n : ℕ} (P : Fin n → Finset ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (M : Finset (Fin n → ℕ)) (F : Finset (List ℕ)) (hF : F ⊆ boxWords P M) :
    (∑ ps∈F,prefixWeight ps)=∑ m∈M,selectedWordMass P m F := by
  have he : F=M.biUnion (fun m => (wordBox P m).filter (fun ps => ps∈F)) := by
    ext ps
    constructor
    · intro hp
      obtain ⟨m,hm,hps⟩ := Finset.mem_biUnion.mp (hF hp)
      exact Finset.mem_biUnion.mpr ⟨m,hm,Finset.mem_filter.mpr ⟨hps,hp⟩⟩
    · intro hp
      obtain ⟨_m,_hm,hps⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_filter.mp hps).2
  calc
    _ = ∑ ps∈M.biUnion (fun m => (wordBox P m).filter (fun ps => ps∈F)),prefixWeight ps := by rw [← he]
    _ = ∑ m∈M,∑ ps∈(wordBox P m).filter (fun ps => ps∈F),prefixWeight ps := by
      apply Finset.sum_biUnion
      intro m _hm m' _hm' hne
      exact (wordBoxes_disjoint P hd m m' hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    _ = _ := Finset.sum_congr rfl (fun m _ => filtered_word_box_mass P m hd F)

theorem unlisted_geometric_box_mass {w top xi Cs C B K L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (a : ℕ → ℕ) (z : PrimeHistories.Node)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (F : Finset (List ℕ)) :
    let U := unlistedGeometric hw htop hxi Cs C B K L alpha beta a z Q F
    (∑ ps∈U,prefixWeight ps)=∑ m∈geometricBoxes hw htop hxi C B K L alpha beta z,
      selectedWordMass (globalBins w top xi) m U := by
  dsimp only
  apply filtered_box_mass _ (fun k l hkl => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl)
  intro ps hp
  have hg := (Finset.mem_inter.mp (Finset.mem_filter.mp hp).1).2
  have hr := (Finset.mem_filter.mp hg).1
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hr).1
  apply Finset.mem_biUnion.mpr
  refine ⟨wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps,
    Finset.mem_image.mpr ⟨ps,hg,rfl⟩,?_⟩
  exact Finset.mem_image.mpr ⟨wordSelection (label (zero_lt_one.trans hw) htop hxi) ps,
    wordSelection_mem hw htop hxi ps hd.2,wordSelection_recovers _ ps hd.1⟩
end NumberTheoryLean.FilteredBoxWordMass



namespace NumberTheoryLean.SoftWitnessCapture
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseAlignment
open ActualWordSelection FiniteBoxWordMass FullIsolatedCofactor EligibleBoxLists
open ExpandedCompactPartition ActualBinOwners SingletonBinSelection TwoPrimeObservableSum
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

theorem word_selection_descending {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) :
    wordSelection (label (zero_lt_one.trans hw) htop hxi) (descendingWord f)=f := by
  have hrec := wordSelection_mem hw htop hxi (descendingWord f) (word_source_membership hw htop hxi m f hf)
  apply word_injective (globalBins w top xi)
    (fun k l hkl => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl)
    _ f (fun k => ((mem_selections _ _ _).mp hrec k).1) (fun k => ((mem_selections _ _ _).mp hf k).1)
  exact wordSelection_recovers _ _ (descendingWord_strict f)

theorem word_multiplicity_descending {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) :
    wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) (descendingWord f)=m := by
  funext k
  unfold wordMultiplicity
  rw [word_selection_descending hw htop hxi m f hf]
  exact ((mem_selections _ _ _).mp hf k).2

theorem soft_full_word_listed {w top xi Cs : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℝ)
    (M : Finset (Fin (binCount w top xi) → ℕ))
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (m : Fin (binCount w top xi) → ℕ) (hm : m∈M) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (i : Fin (binCount w top xi)) (hi : m i=1)
    (a : ℕ → ℕ) (q : ℚ) (hq : q∈Q m) (helig : eligible Y w Cs q)
    (ha : ∀ p∈(pickedPrime f i*selectionProduct (eraseSelection f i)).primeFactors,
      Cs < primeExponent w p → aligns (SourceStopPredicate.sourceClass a) q p) :
    listedWord hw htop hxi Cs a (eligibleLists Y w Cs M Q) (descendingWord f) := by
  unfold listedWord
  rw [word_multiplicity_descending hw htop hxi m f hf]
  exact ⟨q,soft_witness_in_eligibleLists Y w Cs M Q m hm q hq helig,
    full_cofactor_alignment_word hw htop hxi m f hf i hi _ q ha⟩

theorem unlisted_has_no_soft_witness {w top xi Cs C B K L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℝ)
    (M : Finset (Fin (binCount w top xi) → ℕ))
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (m : Fin (binCount w top xi) → ℕ) (hm : m∈M) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (i : Fin (binCount w top xi)) (hi : m i=1)
    (a : ℕ → ℕ) (z : PrimeHistories.Node) (F : Finset (List ℕ))
    (hu : descendingWord f∈unlistedGeometric hw htop hxi Cs C B K L alpha beta a z (eligibleLists Y w Cs M Q) F)
    (q : ℚ) (hq : q∈Q m) :
    ¬(eligible Y w Cs q ∧
      ∀ p∈(pickedPrime f i*selectionProduct (eraseSelection f i)).primeFactors,
        Cs < primeExponent w p → aligns (SourceStopPredicate.sourceClass a) q p) := by
  rintro ⟨helig,ha⟩
  exact (Finset.mem_filter.mp hu).2 (soft_full_word_listed hw htop hxi Y M Q m hm f hf i hi a q hq helig ha)
end NumberTheoryLean.SoftWitnessCapture



namespace ErdosVarianceEligible
open NumberTheoryLean ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection TwoPrimeObservableSum
  FullIsolatedCofactor ActualBinOwners SourceStopPredicate ActualCountErrorEdges
  ErdosVarianceSmallPrime ErdosVarianceCommon ErdosInverseAlignment
  LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

def eligibleWordWitness (Y : ℕ) (w Cs : ℝ) (residue : ℕ → ℕ) (Q : Finset ℚ) (ps : List ℕ) : Prop :=
  ∃ r ∈ Q,eligible (Y : ℝ) w Cs r ∧
    ∀ p ∈ ps,Cs < primeExponent w p → aligns (sourceClass residue) r p

theorem eligible_word_witness_of_endpoint {w top xi Cs : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℕ)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (i : Fin (binCount w top xi)) (hi : m i = 1)
    (residue : ℕ → ℕ) (Q : Finset ℚ) (r : ℚ) (hr : r ∈ Q)
    (hsoft : (r.den : ℝ) ≤ w^Cs ∧ (r.num.natAbs : ℝ) ≤ (Y : ℝ)*w^(Cs+2) ∧
      ∀ t ∈ (pickedPrime f i*selectionProduct (eraseSelection f i)).primeFactors,
        Cs < Real.logb w (t : ℝ) → aligns (fun u => (residue u : ℤ)) r t) :
    eligibleWordWitness Y w Cs residue Q (descendingWord f) := by
  refine ⟨r,hr,⟨hsoft.1,hsoft.2.1⟩,?_⟩
  apply full_cofactor_alignment_word hw htop hxi m f hf i hi (sourceClass residue) r
  intro p hp hhigh
  exact hsoft.2.2 p hp hhigh

theorem word_error_bad_aligning_prime {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℕ)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (i : Fin (binCount w top xi)) (hi : m i = 1)
    (residue : ℕ → ℕ) (r : ℚ) (eps : ℝ) (halign : aligns (sourceClass residue) r (pickedPrime f i))
    (hbad : eps < |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
      (SmallSieveFinite.smallEuler ⌊w⌋₊) (descendingWord f)|) :
    pickedPrime f i ∈ badAligningPrimes (globalBins w top xi i) Y w residue r
      (selectionProduct (eraseSelection f i)) eps := by
  obtain ⟨p,hp,hfi,_hfill⟩ := singleton_selection_recovery _ m i hi f hf
  have hpmem : pickedPrime f i ∈ globalBins w top xi i := by simpa [pickedPrime,hfi] using hp
  have hprod := full_word_isolated_product hw htop hxi m f hf i hi
  apply (mem_badAligningPrimes _ _ _ _ _ _ _ _).mpr
  refine ⟨hpmem,halign,?_⟩
  simpa only [wordCountError,relativeCountError,hprod,Nat.cast_mul,referenceCount] using hbad

end ErdosVarianceEligible



namespace NumberTheoryLean.EligibleListWord
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseAlignment
open ActualWordSelection SoftWitnessCapture EligibleBoxLists ExpandedCompactPartition ActualBinOwners
open LogarithmicBinScale LogarithmicBinLabels
open ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

theorem listed_word_eligible_iff {w top xi Cs : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℝ)
    (M : Finset (Fin (binCount w top xi) → ℕ))
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (a : ℕ → ℕ) (ps : List ℕ) :
    listedWord hw htop hxi Cs a (eligibleLists Y w Cs M Q) ps ↔
      wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps∈M ∧
      ∃ q∈Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),eligible Y w Cs q ∧
        ∀ p∈ps,Cs < primeExponent w p → aligns (SourceStopPredicate.sourceClass a) q p := by
  unfold listedWord
  constructor
  · rintro ⟨q,hq,ha⟩
    obtain ⟨hm,hq,he⟩ := (mem_eligibleLists _ _ _ _ _ _ _).mp hq
    exact ⟨hm,q,hq,he,ha⟩
  · rintro ⟨hm,q,hq,he,ha⟩
    exact ⟨q,(mem_eligibleLists _ _ _ _ _ _ _).mpr ⟨hm,hq,he⟩,ha⟩

theorem listed_selection_eligible_iff {w top xi Cs : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℝ)
    (M : Finset (Fin (binCount w top xi) → ℕ))
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (m : Fin (binCount w top xi) → ℕ) (hm : m∈M) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (a : ℕ → ℕ) :
    listedWord hw htop hxi Cs a (eligibleLists Y w Cs M Q) (descendingWord f) ↔
      ∃ q∈Q m,eligible Y w Cs q ∧
        ∀ p∈descendingWord f,Cs < primeExponent w p → aligns (SourceStopPredicate.sourceClass a) q p := by
  rw [listed_word_eligible_iff hw htop hxi Y M Q a,word_multiplicity_descending hw htop hxi m f hf]
  exact and_iff_right hm

theorem unlisted_compact_selected_data {w top xi Cs C B K L alpha beta eps : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℕ)
    (M : Finset (Fin (binCount w top xi) → ℕ))
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (m : Fin (binCount w top xi) → ℕ) (hm : m∈M) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (a : ℕ → ℕ) (z : PrimeHistories.Node)
    (F : Finset (List ℕ))
    (hu : descendingWord f∈unlistedGeometric hw htop hxi Cs C B K L alpha beta a z (eligibleLists Y w Cs M Q)
      (CountErrorClassification.badCompactWords w K eps Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a
        (SmallSieveFinite.smallEuler ⌊w⌋₊) z F)) :
    descendingWord f∈GeometricRegularWords.geometricWords hw htop hxi C B K L alpha beta z ∧
      eps < |ActualCountErrorEdges.wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a
        (SmallSieveFinite.smallEuler ⌊w⌋₊) (descendingWord f)| ∧
      ¬∃ q∈Q m,eligible Y w Cs q ∧
        ∀ p∈descendingWord f,Cs < primeExponent w p → aligns (SourceStopPredicate.sourceClass a) q p := by
  obtain ⟨hmem,hnot⟩ := Finset.mem_filter.mp hu
  have hh := Finset.mem_inter.mp hmem
  refine ⟨hh.2,(Finset.mem_filter.mp hh.1).2.2,?_⟩
  exact fun hwit => hnot ((listed_selection_eligible_iff hw htop hxi Y M Q m hm f hf a).mpr hwit)
end NumberTheoryLean.EligibleListWord



namespace ErdosVarianceEligible
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership ActualCountErrorEdges
  GeometricRecentWitness GeometricRegularWords BoundedEdgeBins
  ErdosCofactorChoices ErdosSubsetWord ErdosInverseCounts TwoPrimeObservableSum ParentTailPartition
  LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

theorem geometric_selection_recent_witness (K eps : ℝ) (hK : 3 ≤ K) (heps : 0 < eps) :
    ∃ Kstar B0 w0 : ℝ,K+10 < Kstar ∧ 3 ≤ B0 ∧ 1 < w0 ∧
    ∀ (B w top : ℝ),B0 ≤ B → w0 ≤ w → ∀ (hw : 1 < w) (htop : w < top),
      ∀ (xi : ℝ) (hxi : 0 < xi) (C : ℝ),1 ≤ C → Real.log B ≤ 2*Real.log w →
      ∀ (aStar alpha beta : ℝ),0 ≤ aStar → aStar ≤ 1 → ∀ Y : ℕ,0 < Y → ∀ z : Node,
      z.gap = Real.log (Y : ℝ)/Real.log w-aStar+2 → z.side = .even → 199/100 ≤ z.ratio →
      Consistent z → z.cutoff = B → z.closed = true → w^B = top →
      ∀ (residue : ℕ → ℕ) (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ),
      f ∈ selections (globalBins w top xi) m →
      descendingWord f ∈ geometricWords hw htop hxi C B K (2*Kstar+5) alpha beta z →
      eps < |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) (descendingWord f)| →
      ∃ j : Fin (binCount w top xi),boundedEdgeBin w top xi Y m (2*Kstar+3) (2*Kstar+3) j ∧
        ∀ i : Fin (binCount w top xi),m i = 1 → j < i →
        WitnessingBadEdge Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
          (eps/(4*(⌈2*Kstar+10⌉₊ : ℝ))) (SmallSieveFinite.smallEuler ⌊w⌋₊)
          (pickedPrime f i) (selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j) := by
  obtain ⟨Kstar,B0,w0,hKs,hB0,hw0,hcore⟩ := geometric_recent_witness K eps hK heps
  refine ⟨Kstar,B0,w0,hKs,hB0,hw0,?_⟩
  intro B w top hB hw0' hw htop xi hxi C hC hcomp aStar alpha beta ha0 ha1 Y hY z hroot
    heven h199 hz hcut hclosed hpower residue m f hf hgeom hbad
  have hh := hcore B w top hB hw0' hw htop xi hxi C hC hcomp aStar alpha beta ha0 ha1 Y hY z hroot
    heven h199 hz hcut hclosed hpower residue (descendingWord f) hgeom hbad
  simpa only [SoftWitnessCapture.word_multiplicity_descending hw htop hxi m f hf,
    SoftWitnessCapture.word_selection_descending hw htop hxi m f hf] using hh

end ErdosVarianceEligible



open _root_.Filter
namespace ErdosVarianceEligible
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
  SafeSubsetBoxGeometry BoundedEdgeBins ParentCofactorChoices ParentTailPartition
  RawBoxRationalWitness SingletonBinSelection TwoPrimeObservableSum ActualCountErrorEdges
  ErdosCofactorChoices ErdosSubsetWord ErdosVarianceWeighted ErdosVarianceEffective ErdosInverseBoxHeight
  ErdosInverseCells ErdosInverseAlignment ErdosInverseBoxApplication ErdosInverseSampleCost ErdosInverseCounts
  LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinPartition
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem outside_exceptions_eligible_word (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) :
    ∀ᶠ top : ℝ in atTop,
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → 2*C*xi ≤ 1 →
      ∀ (hw : 1 < sourceW top) (htop : sourceW top < top) (K aStar X : ℝ),0 ≤ aStar →
      ∀ z : Node,0 < sourceY top →
        z.gap = Real.log (sourceY top : ℝ)/Real.log (sourceW top)-aStar+2 →
        Valid z.side z.ratio → Consistent z → StrongState z → z.closed = true → (sourceW top)^z.cutoff = top →
      ∀ m : Fin (binCount (sourceW top) top xi) → ℕ,SafeAnchor hw htop hxi C (sourceB top) K z m →
      ∀ f ∈ selections (globalBins (sourceW top) top xi) m,
      ∀ i : Fin (binCount (sourceW top) top xi),m i = 1 →
      ∀ J : Finset (Fin (binCount (sourceW top) top xi)),
        (∀ j ∈ J,boundedEdgeBin (sourceW top) top xi (sourceY top) m M X j ∧ j < i) →
      ∀ (residue : ℕ → ℕ) (delta cp sigma Cs eps : ℝ) (F : ℕ),
        (∀ j ∈ J,SourceInverseConclusion (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊)
          residue delta (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊)
          (cofactorScale top xi (parentCofactorMultiplicity m i j)) (lower (sourceW top) top xi i) (sourceZ top) cp sigma F
          (globalBins (sourceW top) top xi i)
          (cofactorChoices (globalBins (sourceW top) top xi) (parentCofactorMultiplicity m i j)) (globalBins (sourceW top) top xi j)) →
        (∃ j ∈ J,WitnessingBadEdge (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊) residue delta
          (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) (pickedPrime f i)
          (selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)) →
        eps < |wordCountError (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊) residue
          (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) (descendingWord f)| →
        (¬∃ j ∈ J,actualWitness (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊) residue delta
          (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) (globalBins (sourceW top) top xi i)
          (cofactorScale top xi (parentCofactorMultiplicity m i j)) (lower (sourceW top) top xi i) (sourceZ top) cp
          (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)) →
        let Q := rawBoxList (globalBins (sourceW top) top xi) i J residue
          (fun j => cofactorScale top xi (parentCofactorMultiplicity m i j)) (lower (sourceW top) top xi i) (sourceZ top) cp
        ¬hardSelection Q top (lower (sourceW top) top xi i) (width (sourceW top) top xi i) residue i Cs eps f →
        eligibleWordWitness (sourceY top) (sourceW top) Cs residue Q (descendingWord f) := by
  filter_upwards [structured_endpoint_heights C M hC hM,
    ErdosInverseEuler.sourceW_tendsto_atTop.eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually JacobsthalSourceScale.source_scale_eventually]
    with top hheight hw2 hscale
  intro xi hxi hxi1 hDelta hw htop K aStar X ha z hY hroot hs hz hg hclosed hcap m hanchor
    f hf i hi J hJ residue delta cp sigma Cs eps F hInv hbadEdge hbadWord hnoInv
  dsimp only
  intro hnoHard
  let P := globalBins (sourceW top) top xi
  let S := fun j => cofactorScale top xi (parentCofactorMultiplicity m i j)
  let R := lower (sourceW top) top xi i
  let Q := rawBoxList P i J residue S R (sourceZ top) cp
  have hj : ∀ j ∈ J,m j = 1 := fun j hj => bounded_edge_singleton m j (hJ j hj).1
  obtain ⟨j,hjJ,r,hrQ,hrLocal,halign,hstructure⟩ := raw_box_witness P m i J f hf hi hj
    (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊) residue delta
    (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) S R (sourceZ top) cp sigma F hInv hbadEdge hnoInv
  have hbounds := hheight xi hxi hxi1 hDelta hw htop K aStar X ha z hY hroot hs hz hg hclosed hcap
    m hanchor f hf i j (hJ j hjJ).2 hi (hJ j hjJ).1 residue r cp hrLocal hstructure
  have hcomp : Real.log (sourceB top) ≤ 2*Real.log (sourceW top) := hscale.2.2.2.2
  have hdata := full_endpoint_data hw htop hxi hC ha hcomp (sourceY top) hY z hroot hs hz hg hclosed hcap
    m hanchor f hf i hi
  have hR : 0 < R := (zero_lt_one.trans hw).trans_le (bin_source_bounds (zero_lt_one.trans hw) htop hxi i).1
  have hwidth : 0 ≤ width (sourceW top) top xi i := (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le
  have hRp := ((ErdosInversePrimeBin.mem_primeBin hR.le hwidth (pickedPrime f i)).mp hdata.2.2.1).2.1.le
  have hbad := word_error_bad_aligning_prime hw htop hxi (sourceY top) m f hf i hi residue r eps halign hbadWord
  have hsoft := endpoint_soft_conclusion Q top R (width (sourceW top) top xi i) residue f i r Cs eps
    hrQ hdata.1 hdata.2.1 hR hRp hw2 hdata.2.2.2 hbounds.1 hbounds.2 hbad hnoHard
  exact eligible_word_witness_of_endpoint hw htop hxi (sourceY top) m f hf i hi residue Q r hrQ hsoft

end ErdosVarianceEligible


end Erdos970

end OAI
