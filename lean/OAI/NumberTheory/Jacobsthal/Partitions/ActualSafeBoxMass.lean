import OAI.NumberTheory.Jacobsthal.Paths.FiniteBoxWordMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SafeSubsetBoxGeometry
open FinitePathGeometry PrimeHistories SourceStopPredicate RepresentativeAdmission RepresentativeTraceInvariance
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open ReferenceAdmission ErdosCofactorChoices ErdosSubsetWord
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

noncomputable def SafeAnchor {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Clen B K : ℝ) (z : Node) (mult : Fin (binCount w top xi) → ℕ) : Prop :=
  ∃ anchor ∈ selections (globalBins w top xi) mult,
    ((descendingWord anchor).length:ℝ) ≤ Clen*Real.log B ∧
    representativeSafe w (representative w (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi)) z (2*Clen*xi) (descendingWord anchor) ∧
    (terminal w z (descendingWord anchor)).gap ≤ K

theorem selection_representatives_eq {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f g : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) (hg : g ∈ selections (globalBins w top xi) mult) :
    (descendingWord f).map (representative w (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi))=
      (descendingWord g).map (representative w (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi)) := by
  have hh := congrArg (List.map (fun b => PrimeBinRepresentatives.rightExponent w (lower w top xi b) (width w top xi b)))
    (selection_label_word_eq hw htop hxi mult f g hf hg)
  unfold representative
  simpa only [List.map_map,Function.comp_def] using hh

theorem anchored_choice_geometry {w top xi B Clen K : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ Clen) (hcomp : Real.log B ≤ 2*Real.log w) (z : Node)
    (mult : Fin (binCount w top xi) → ℕ) (hanchor : SafeAnchor hw htop hxi Clen B K z mult)
    (f : Fin (binCount w top xi) → Finset ℕ) (hf : f ∈ selections (globalBins w top xi) mult) :
    descendingWord f ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap ∧
      (terminal w z (descendingWord f)).gap ≤ K+2*Clen*xi := by
  obtain ⟨g,hg,hlen,hSafe,hK⟩ := hanchor
  let rep := representative w (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi)
  have he := selection_representatives_eq hw htop hxi mult f g hf hg
  have hsf : representativeSafe w rep z (2*Clen*xi) (descendingWord f) :=
    (representativeSafe_map_iff w rep z (2*Clen*xi) _ _ he).mpr hSafe
  have hsource := word_source_membership hw htop hxi mult f hf
  have hsourceg := word_source_membership hw htop hxi mult g hg
  have hadmit : admitted w z.side z.gap (descendingWord f) := by
    apply finite_safe_admits w rep z (2*Clen*xi) _ (by positivity) _ hsf
    intro p hp
    have hh := (source_representative_error hw htop hxi (hsource p hp)).1
    change 0 ≤ rep p-primeExponent w p at hh
    linarith
  refine ⟨Finset.mem_filter.mpr ⟨mem_decreasingPrefixes.mpr ⟨descendingWord_strict f,hsource⟩,hadmit⟩,?_⟩
  have hlength : (descendingWord f).length=(descendingWord g).length :=
    (global_word_length hw htop hxi mult f hf).trans (global_word_length hw htop hxi mult g hg).symm
  have hlenf : ((descendingWord f).length:ℝ) ≤ Clen*Real.log B := by rwa [hlength]
  have hmf := source_prefix_movement hw htop hxi hC hcomp z (descendingWord f) hsource hlenf
  have hmg := source_prefix_movement hw htop hxi hC hcomp z (descendingWord g) hsourceg hlen
  have hgap : representativeGap rep z.gap (descendingWord f)=representativeGap rep z.gap (descendingWord g) := by
    unfold representativeGap
    rw [he]
  change 0 ≤ (terminal w z (descendingWord f)).gap-representativeGap rep z.gap (descendingWord f) ∧
    (terminal w z (descendingWord f)).gap-representativeGap rep z.gap (descendingWord f) ≤ 2*Clen*xi at hmf
  change 0 ≤ (terminal w z (descendingWord g)).gap-representativeGap rep z.gap (descendingWord g) ∧
    (terminal w z (descendingWord g)).gap-representativeGap rep z.gap (descendingWord g) ≤ 2*Clen*xi at hmg
  rw [hgap] at hmf
  linarith [hmf.2,hmg.1]
end NumberTheoryLean.SafeSubsetBoxGeometry



namespace NumberTheoryLean.ActualSafeBoxMass
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open LogarithmicBinScale LogarithmicBinPartition ReferenceAdmission StrongSourceFamilies
open SafeSubsetBoxGeometry FiniteBoxWordMass CanonicalSubsetBox ErdosSubsetWord

attribute [local instance] Classical.propDecidable

theorem uniform_safe_box_mass (K : ℝ) (hK : 3 ≤ K) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧ ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w →
      ∀ (hw : 1 < w) (htop : w < top) (xi Clen : ℝ) (hxi : 0 < xi),0 ≤ Clen →
      Real.log B ≤ 2*Real.log w → 2*Clen*xi ≤ 1 → ∀ z : Node,
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B →
      z.closed=true → w^B=top → ∀ M : Finset (Fin (binCount w top xi) → ℕ),
      (∀ mult ∈ M,SafeAnchor hw htop hxi Clen B K z mult) →
      B^2*(∑ mult ∈ M,selectionMass (globalBins w top xi) mult) ≤ C := by
  obtain ⟨C,B₀,w₀,hC,hB₀,hw₀,hbound⟩ := uniform_source_family_mass (K+1) 2 (by linarith) (by norm_num)
  refine ⟨C,B₀,w₀,hC,hB₀,hw₀,?_⟩
  intro B w top hB hw hw1 htop xi Clen hxi hClen hcomp hsmall z hi h199 h23 hz hcut hclosed hcap M hanchors
  have hd : Pairwise (fun i j => Disjoint (globalBins w top xi i) (globalBins w top xi j)) :=
    fun i j hij => bins_pairwise_disjoint (zero_lt_one.trans hw1) htop hxi i j hij
  let F := boxWords (globalBins w top xi) M
  have hF : F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap := by
    intro ps hps
    obtain ⟨mult,hm,hword⟩ := Finset.mem_biUnion.mp hps
    obtain ⟨f,hf,he⟩ := Finset.mem_image.mp hword
    have hh := (anchored_choice_geometry hw1 htop hxi hClen hcomp z mult (hanchors mult hm) f hf).1
    rwa [he] at hh
  have hFK : ∀ ps ∈ F,(terminal w z ps).gap ≤ K+1 := by
    intro ps hps
    obtain ⟨mult,hm,hword⟩ := Finset.mem_biUnion.mp hps
    obtain ⟨f,hf,he⟩ := Finset.mem_image.mp hword
    have hh := (anchored_choice_geometry hw1 htop hxi hClen hcomp z mult (hanchors mult hm) f hf).2
    rw [he] at hh
    linarith
  rw [total_box_mass_eq (globalBins w top xi) hd M]
  exact hbound B w top hB hw htop hcomp z hi h199 h23 hz hcut hclosed hcap F hF hFK
end NumberTheoryLean.ActualSafeBoxMass


end Erdos970

end OAI
