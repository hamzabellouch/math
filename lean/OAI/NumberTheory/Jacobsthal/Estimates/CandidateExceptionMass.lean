import OAI.NumberTheory.Jacobsthal.Partitions.GeometricRangeInverse
import OAI.NumberTheory.Jacobsthal.Primes.LatePrimeRatio

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.MultiplicitySuffixRank
open BinCutSelections

attribute [local instance] Classical.propDecidable

noncomputable def lowerIndices {n : ℕ} (j : Fin n) : Finset (Fin n) := Finset.univ.filter (fun k => k<j)
noncomputable def suffixRank {n : ℕ} (m : Fin n → ℕ) (j : Fin n) : ℕ := 1+∑ k ∈ lowerIndices j,m k

theorem below_total_rank {n : ℕ} (m : Fin n → ℕ) (j : Fin n) :
    1+∑ k,belowMultiplicity m j k=suffixRank m j := by
  simp only [suffixRank,lowerIndices,Finset.sum_filter,belowMultiplicity]

theorem suffixRank_pos {n : ℕ} (m : Fin n → ℕ) (j : Fin n) : 0 < suffixRank m j := by
  unfold suffixRank
  omega

theorem suffixRank_strict {n : ℕ} (m : Fin n → ℕ) (j k : Fin n) (hjk : j<k) (hmj : 0 < m j) :
    suffixRank m j < suffixRank m k := by
  have hnot : j ∉ lowerIndices j := by simp [lowerIndices]
  have hsub : insert j (lowerIndices j) ⊆ lowerIndices k := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · simp [lowerIndices,hjk]
    · have hh := (Finset.mem_filter.mp hb).2
      simp [lowerIndices,hh.trans hjk]
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => Nat.zero_le (m b))
  rw [Finset.sum_insert hnot] at hsum
  unfold suffixRank
  omega

theorem suffixRank_injective_singletons {n : ℕ} (m : Fin n → ℕ) :
    Set.InjOn (suffixRank m) {j | m j=1} := by
  intro j hj k hk he
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · have hh := suffixRank_strict m j k hjk (by change m j=1 at hj; omega)
    omega
  · rfl
  · have hh := suffixRank_strict m k j hkj (by change m k=1 at hk; omega)
    omega

theorem singleton_card_le_rank {n : ℕ} (m : Fin n → ℕ) (J : Finset (Fin n)) (H : ℕ)
    (hm : ∀ j ∈ J,m j=1) (hH : ∀ j ∈ J,suffixRank m j ≤ H) : J.card ≤ H := by
  have hinj : Set.InjOn (suffixRank m) (J : Set (Fin n)) :=
    fun j hj k hk he => suffixRank_injective_singletons m (hm j hj) (hm k hk) he
  have hsub : J.image (suffixRank m) ⊆ Finset.Icc 1 H := by
    intro r hr
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_Icc.mpr ⟨suffixRank_pos m j,hH j hj⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hh
  simpa using hh
end NumberTheoryLean.MultiplicitySuffixRank



namespace NumberTheoryLean.BoundedEdgeSuffixRank
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport StrongSourceFamilies
open ErdosCofactorChoices ErdosSubsetWord BoundedEdgeBins FullBoxLengthBounds BinCutSelections SelectionWordSplit
open MultiplicitySuffixRank SafeSubsetBoxGeometry RepresentativeAdmission
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem list_length_le_exponents (w : ℝ) (ps : List ℕ) (hp : ∀ p ∈ ps,1 ≤ primeExponent w p) :
    (ps.length:ℝ) ≤ (ps.map (primeExponent w)).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hh := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))
    have hp1 := hp p (by simp)
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,List.map_cons,List.sum_cons]
    linarith

theorem bounded_edge_rank_le {w top xi B C K a M X : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (ha0 : 0 ≤ a) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m)
    (j : Fin (binCount w top xi)) (hj : boundedEdgeBin w top xi Y m M X j) :
    suffixRank m j ≤ ⌈M⌉₊ := by
  obtain ⟨f,hf,u,hfu,hparent,_hx⟩ := hj
  have hword := selected_word_split hw htop hxi m f hf j u hfu
  have hfull := (anchored_choice_geometry hw htop hxi hC hcomp z m ha f hf).1
  have hfloor := (source_reference_transport hw htop z hs hz hg hclosed hcap _ hfull).2
  have hsource := word_source_membership hw htop hxi m f hf
  have hsuffix : ∀ p ∈ u::descendingWord (belowSelection f j),1 ≤ primeExponent w p := by
    intro p hp
    have hpfull : p ∈ descendingWord f := by rw [hword]; exact List.mem_append_right _ hp
    have hpw := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hsource p hpfull)
    change 1 ≤ Real.log (p:ℝ)/Real.log w
    exact ((one_lt_div (Real.log_pos hw)).mpr (Real.log_lt_log (zero_lt_one.trans hw) hpw.2.1)).le
  have hlength := list_length_le_exponents w (u::descendingWord (belowSelection f j)) hsuffix
  have hgap : (terminal w z (descendingWord f)).gap=
      (terminal w z (descendingWord (aboveSelection f j))).gap-
        ((u::descendingWord (belowSelection f j)).map (primeExponent w)).sum := by
    rw [hword,terminal_append]
    exact terminal_gap_sum w _ _
  have hpar := parent_length_gap hw htop hxi Y hY z hroot m f hf j
  have hrank : suffixRank m j=(u::descendingWord (belowSelection f j)).length := by
    rw [← below_total_rank,List.length_cons,global_word_length hw htop hxi _ _ (below_selection_mem _ m f hf j)]
    omega
  have hreal : (suffixRank m j:ℝ) ≤ M := by rw [hrank]; nlinarith
  exact_mod_cast (hreal.trans (Nat.le_ceil M))
end NumberTheoryLean.BoundedEdgeSuffixRank



namespace NumberTheoryLean.BoundedCandidateCount
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
open SafeSubsetBoxGeometry GeometricBoxImages BoundedEdgeBins BoundedEdgeSuffixRank MultiplicitySuffixRank
open LogarithmicBinScale LogarithmicBinLabels

attribute [local instance] Classical.propDecidable

noncomputable def candidateBins (w top xi : ℝ) (Y : ℕ) (m : Fin (binCount w top xi) → ℕ) (M X : ℝ) :
    Finset (Fin (binCount w top xi)) := Finset.univ.filter (boundedEdgeBin w top xi Y m M X)

theorem candidate_bins_card_le {w top xi B C K a M X : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (ha0 : 0 ≤ a) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m) :
    (candidateBins w top xi Y m M X).card ≤ ⌈M⌉₊ := by
  apply singleton_card_le_rank m _ _
  · intro j hj
    exact bounded_edge_singleton m j (Finset.mem_filter.mp hj).2
  · intro j hj
    exact bounded_edge_rank_le hw htop hxi hC hcomp ha0 Y hY z hroot hs hz hg hclosed hcap m ha j (Finset.mem_filter.mp hj).2
end NumberTheoryLean.BoundedCandidateCount



namespace NumberTheoryLean.RecentReferenceSegment
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission StrongReferenceTransport StrongSourceFamilies ActualPrimeHigh
open SourceFirstCrossing WordIntervalGeometry LatePrimeRatio BoundedEdgeSuffixRank ActualReferencePrefixes
open LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem recent_reference_segment {w top B K Kstar a : ℝ} (hw : 1 < w) (htop : w < top)
    (hK : 3 ≤ K) (hKstar : K+10 ≤ Kstar) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hB3 : 3 ≤ B) (hBlarge : 2*(Kstar+2-a) ≤ B)
    (Y : ℕ) (hY : 0 < Y) (z : Node) (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hi : z.side=.even) (h199 : 199/100 ≤ z.ratio) (hz : Consistent z) (hcut : z.cutoff=B)
    (hclosed : z.closed=true) (hpower : w^B=top) (ps : List ℕ)
    (hps : ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap)
    (hend : (terminal w z ps).gap ≤ K) :
    ∃ pre rest : List ℕ,ps=pre++rest ∧ pre ≠ [] ∧ rest ≠ [] ∧
      Kstar < wordIntervalExponent w Y pre ∧ rest.length ≤ ⌈2*Kstar+10⌉₊ ∧
      ∀ before u after,rest=before++u::after →
        wordIntervalExponent w Y (pre++before) ≤ 2*Kstar+3 ∧
        a ≤ wordIntervalExponent w Y ((pre++before)++[u]) ∧
        primeExponent w u ≤ 2*Kstar+3 ∧ (terminal w z (pre++before)).gap ≤ 2*Kstar+5 := by
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB3 z hi h199 hz hcut
  have hcap : w^z.cutoff=top := by rwa [hcut]
  have hu := (source_reference_transport hw htop z hs hz hg hclosed hcap ps hps).1
  have hua := (mem_uncappedPrefixes hw z ps).mp hu
  obtain ⟨S,_hS,ha⟩ := (uncapped_iff_exists_ceiling w 1 z ps).mp hua
  have hBp : 0 < B := by linarith
  let H := Kstar+2-a
  have hH : 0 < H := by dsimp [H]; linarith
  have htheta : H/B ≤ 1/2 := by apply (div_le_iff₀ hBp).mpr; dsimp [H]; linarith
  have hthetaB : (H/B)*B=H := div_mul_cancel₀ H hBp.ne'
  have he : (terminal w z ps).gap ≤ (H/B)*B := by rw [hthetaB]; dsimp [H]; linarith
  obtain ⟨pre,p,tail,hpre,hword,_hbefore,hcross,_hlo⟩ :=
    source_gap_crossing (by norm_num) hBp htheta z hs h199 hz hcut ps ha he
  rw [hthetaB] at hcross _hbefore
  have hword' : ps=(pre++[p])++tail := by simpa only [List.append_assoc,List.singleton_append] using hword
  have hac : allowed w 1 S z (pre++[p]) := ((allowed_append w 1 S z (pre++[p]) tail).mp (hword' ▸ ha)).1
  have hlen : 2 ≤ (pre++[p]).length := by have hh := List.length_pos_iff.mpr hpre; simp only [List.length_append,List.length_singleton]; omega
  have hlate := allowed_late_gap_cutoff hw (by norm_num : (1:ℝ)≤1) z (pre++[p]) hac hlen
  have hxc : (terminal w z (pre++[p])).cutoff=primeExponent w p := by simp [terminal,step]
  have hrc : (terminal w z (pre++[p])).gap=(terminal w z pre).gap-primeExponent w p := by simp [terminal,step]
  rw [hxc] at hlate
  have hpreGap : (terminal w z pre).gap ≤ 2*H := by linarith
  have hsrc := (mem_decreasingPrefixes.mp (Finset.mem_filter.mp hps).1).2
  have hpos : ∀ q∈ps,0 < q := fun q hq => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop q).mp (hsrc q hq)).1.pos
  have hexp : ∀ q∈ps,1 ≤ primeExponent w q := by
    intro q hq
    have hqw := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop q).mp (hsrc q hq)
    exact ((one_lt_div (Real.log_pos hw)).mpr (Real.log_lt_log (zero_lt_one.trans hw) hqw.2.1)).le
  have hpreSub : pre ⊆ ps := by intro q hq; rw [hword]; exact List.mem_append_left _ hq
  have hrestSub : p::tail ⊆ ps := by intro q hq; rw [hword]; exact List.mem_append_right _ hq
  have hvpre := word_interval_gap Y hY z hroot pre (fun q hq => hpos q (hpreSub hq))
  have hVpre : wordIntervalExponent w Y pre ≤ 2*Kstar+3 := by dsimp [H] at hpreGap; linarith
  have hhigh : Kstar < wordIntervalExponent w Y pre := by dsimp [H] at _hbefore; linarith
  have hfloor := (source_reference_transport hw htop z hs hz hg hclosed hcap ps hps).2
  have hsum := list_length_le_exponents w (p::tail) (fun q hq => hexp q (hrestSub hq))
  have hfinalGap : (terminal w z ps).gap=(terminal w z pre).gap-((p::tail).map (primeExponent w)).sum := by
    rw [hword,terminal_append]
    exact RepresentativeAdmission.terminal_gap_sum w _ _
  have hrestLength : (p::tail).length ≤ ⌈2*Kstar+10⌉₊ := by
    have hh : ((p::tail).length:ℝ) ≤ 2*Kstar+10 := by linarith
    exact_mod_cast hh.trans (Nat.le_ceil (2*Kstar+10))
  refine ⟨pre,p::tail,hword,hpre,by simp,hhigh,hrestLength,?_⟩
  intro before u after hrest
  have hparword : ps=(pre++before)++u::after := by rw [hword,hrest,List.append_assoc]
  have hchildword : ps=((pre++before)++[u])++after := by simpa only [List.append_assoc,List.singleton_append] using hparword
  have hparSub : pre++before ⊆ ps := by intro q hq; rw [hparword]; exact List.mem_append_left _ hq
  have hchildSub : (pre++before)++[u] ⊆ ps := by intro q hq; rw [hchildword]; exact List.mem_append_left _ hq
  have hbeforeSub : before ⊆ ps := fun q hq => hparSub (List.mem_append_right _ hq)
  have hmono := gap_prefix_mono w z pre before (fun q hq => (hexp q (hbeforeSub hq)).trans' (by norm_num))
  have hvpar := word_interval_gap Y hY z hroot (pre++before) (fun q hq => hpos q (hparSub hq))
  have hvchild := word_interval_gap Y hY z hroot ((pre++before)++[u]) (fun q hq => hpos q (hchildSub hq))
  have hchildin : (pre++before)++[u] ∈ ps.inits := (List.mem_inits _ _).mpr ⟨after,hchildword.symm⟩
  have hchildfloor := reference_prefix_gap_floor hw htop z hs hz hg hclosed hcap ps _ hps hchildin
  have huMem : u ∈ ps := by rw [hparword]; simp
  have hstep := interval_exponent_step w Y hY (pre++before) u
    (List.prod_pos (fun q hq => hpos q (hparSub hq))) (hpos u huMem)
  refine ⟨?_,?_,?_,?_⟩ <;> linarith
end NumberTheoryLean.RecentReferenceSegment



namespace NumberTheoryLean.CandidateExceptionMass
open ErdosCofactorChoices BoxWitnessFactorization CanonicalSubsetBox TwoPrimeObservableSum ParentTailPartition

attribute [local instance] Classical.propDecidable

noncomputable def someWitnessMass {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i : Fin n) (J : Finset (Fin n)) (W : Fin n → (ℕ × ℕ) → ℕ → Prop) : ℝ :=
  ∑ f ∈ (selections P m).filter (fun f => ∃ j∈J,W j (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)),
    (selectionProduct f:ℝ)⁻¹

theorem some_witness_mass_le_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i : Fin n) (J : Finset (Fin n)) (W : Fin n → (ℕ × ℕ) → ℕ → Prop) :
    someWitnessMass P m i J W ≤ ∑ j ∈ J,selectionWitnessMass P m i j (W j) := by
  simp only [someWitnessMass,selectionWitnessMass,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro f _hf
  have hn : 0 ≤ (selectionProduct f:ℝ)⁻¹ := by positivity
  by_cases hex : ∃ j∈J,W j (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)
  · rw [ite_eq_left hex]
    obtain ⟨j,hj,hw⟩ := hex
    have hh := Finset.single_le_sum (fun k _hk =>
      show 0 ≤ if W k (pickedPrime f i,selectionProduct (parentCofactorSelection f i k)) (pickedPrime f k) then (selectionProduct f:ℝ)⁻¹ else 0 from by split_ifs <;> positivity) hj
    simpa only [ite_eq_left hw] using hh
  · rw [ite_eq_right hex]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)

theorem some_witness_mass_bound {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i : Fin n) (J : Finset (Fin n)) (W : Fin n → (ℕ × ℕ) → ℕ → Prop) (sigma : ℝ)
    (h : ∀ j∈J,selectionWitnessMass P m i j (W j) ≤ sigma*selectionMass P m) :
    someWitnessMass P m i J W ≤ (J.card:ℝ)*sigma*selectionMass P m := by
  have hh := (some_witness_mass_le_sum P m i J W).trans (Finset.sum_le_sum h)
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_assoc] using hh

theorem some_witness_mass_card_bound {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i : Fin n) (J : Finset (Fin n)) (W : Fin n → (ℕ × ℕ) → ℕ → Prop) (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (H : ℕ) (hcard : J.card ≤ H)
    (h : ∀ j∈J,selectionWitnessMass P m i j (W j) ≤ sigma*selectionMass P m) :
    someWitnessMass P m i J W ≤ (H:ℝ)*sigma*selectionMass P m := by
  have hm : 0 ≤ selectionMass P m := Finset.sum_nonneg (fun _ _ => by positivity)
  have hc : (J.card:ℝ) ≤ H := by exact_mod_cast hcard
  exact (some_witness_mass_bound P m i J W sigma h).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hsigma) hm)
end NumberTheoryLean.CandidateExceptionMass


end Erdos970

end OAI
