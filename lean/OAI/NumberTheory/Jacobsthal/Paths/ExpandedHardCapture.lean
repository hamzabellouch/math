import OAI.NumberTheory.Jacobsthal.Probability.RegularStoppedEvent

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RegularStoppedMass
open FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate ActualWordSelection ActualRegularBoxes
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ActualRegularAdmission ActualPrefixClearance RegularBadTagWords SourceMarkedStopping
open StoppedTraceSets StoppedCountAdapters PriorPrimeWindow MissingWindowPrimeMass
open StrongReferenceTransport StrongSourceFamilies ActualPrimeHigh ReferenceAdmission
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosInverseAlignment
open RegularStoppedEvent

attribute [local instance] Classical.propDecidable

theorem uncaptured_mass_le_exceptions {w top xi Cs eta Clen B K b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (hmesh : 2*(xi/Real.log w) ≤ 6*(2*Clen*xi))
    (hb₀ : 0 < b₀) (hCs : Cs < 2*b₀) (hsearch : b₁ < w^((1/4:ℝ)))
    (hh : xi/Real.log w ≤ b₀) (hsmall : 2*Clen*xi+(206/100)*(xi/Real.log w) ≤ (4/100)*b₀)
    (Y : ℕ) (a : ℕ → ℕ) (z : Node) (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hg : StrongState z) (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (hroot : b₁/2 < z.cutoff)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) :
    (∑ ps ∈ uncapturedRegular hw htop hxi Y Cs eta Clen B K b₀ b₁ a z Q,prefixWeight ps) ≤
      (∑ ps ∈ regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q (sourceClass a),prefixWeight ps) +
      (∑ ps ∈ missingWindowPrefixes w 1 K b₀ b₁ z,prefixWeight ps) := by
  have hsub := uncaptured_subset_exceptions (eta := eta) (K := K) hw htop hxi hC hcomp hmesh hb₀ hCs hsearch hh hsmall
    Y a z hs hz hg hclosed hcap hroot Q
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ps _ _ => prefixWeight_nonneg ps)).trans
  have he :
      (∑ ps ∈ regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q (sourceClass a) ∪
        missingWindowPrefixes w 1 K b₀ b₁ z,prefixWeight ps) +
      (∑ ps ∈ regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q (sourceClass a) ∩
        missingWindowPrefixes w 1 K b₀ b₁ z,prefixWeight ps) = _ := Finset.sum_union_inter
  have hn : 0 ≤ ∑ ps ∈ regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q (sourceClass a) ∩
    missingWindowPrefixes w 1 K b₀ b₁ z,prefixWeight ps := Finset.sum_nonneg (fun ps _ => prefixWeight_nonneg ps)
  linarith
end NumberTheoryLean.RegularStoppedMass



namespace NumberTheoryLean.StoppedGeometryInvariance
open FinitePathGeometry StoppedCountVertex StoppedCountAdapters StoppedEvaluation StoppedTraceSets
open RegularStoppedEvent SourceStopPredicate LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open LogarithmicBinPartition
open PrimeHistories

attribute [local instance] Classical.propDecidable

theorem traces_eq_of_geometry (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v v' : Vertex)
    (hn : v.node=v'.node) (hp : v.past=v'.past) (ha : v.available=v'.available) :
    traces w stop n v=traces w stop n v' := by
  induction n generalizing v v' with
  | zero =>
    simp only [traces]
    apply ite_cond_congr
    simp only [lowerStop,hn,hp]
  | succ n ih =>
    have hstop : lowerStop stop v ↔ lowerStop stop v' := by simp only [lowerStop,hn,hp]
    have hinc : includedPrimes w v=includedPrimes w v' := by simp only [includedPrimes,hn,ha]
    have hchild : ∀ p,traces w stop n (child w v p)=traces w stop n (child w v' p) := by
      intro p
      exact ih (child w v p) (child w v' p) (by simp only [child,hn])
        (by simp only [child,hp]) (by simp only [child,ha])
    simp only [traces,hstop,hinc,hchild]

theorem root_stopped_independent (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (z : Node)
    (P H H' : Finset ℕ) (mu mu' : ℝ) :
    stopped w stop n (rootVertex z H P mu)=stopped w stop n (rootVertex z H' P mu') :=
  congrArg Prod.snd (traces_eq_of_geometry w stop n _ _ rfl rfl rfl)

theorem hasSourceStop_iff_original_root {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (H : Finset ℕ) (mu : ℝ) :
    hasSourceStop hw htop hxi Y Cs eta Clen B b₀ b₁ a z ps ↔
      ∃ pre tail : List ℕ,ps=pre++tail ∧ pre ∈ stopped w
        (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
          (label (zero_lt_one.trans hw) htop hxi) a z)
        (sourcePrimeSet w top).card (rootVertex z H (sourcePrimeSet w top) mu) := by
  unfold hasSourceStop
  rw [root_stopped_independent w _ _ z (sourcePrimeSet w top) ∅ H 1 mu]
end NumberTheoryLean.StoppedGeometryInvariance



namespace NumberTheoryLean.ExpandedNoStop
open StoppedCountVertex StoppedEvaluation StoppedVertexHistory StoppedTraceSets FirstStopSemantics
open FinitePathGeometry StoppedCountAdapters RegularStoppedEvent StoppedGeometryInvariance
open SourceStopPredicate LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

theorem expanded_no_lower_stop (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ expanded w stop n v) :
    ∀ pre tail : List ℕ,ps=pre++tail → ¬lowerStop stop (after w v pre) := by
  induction n generalizing v ps with
  | zero =>
    unfold expanded at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · exact False.elim (Finset.notMem_empty _ hp)
    · have he : ps=[] := Finset.mem_singleton.mp hp
      subst ps
      intro pre tail heq
      have hpre := (List.append_eq_nil_iff.mp heq.symm).1
      simpa only [hpre,after] using hs
  | succ n ih =>
    unfold expanded at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · exact False.elim (Finset.notMem_empty _ hp)
    · rcases Finset.mem_insert.mp hp with he | hp
      · subst ps
        intro pre tail heq
        have hpre := (List.append_eq_nil_iff.mp heq.symm).1
        simpa only [hpre,after] using hs
      · obtain ⟨p,_hinc,hps⟩ := Finset.mem_biUnion.mp hp
        obtain ⟨qs,hqs,rfl⟩ := Finset.mem_image.mp hps
        intro pre tail heq
        cases pre with
        | nil => exact hs
        | cons q pre =>
          rw [List.cons_append] at heq
          obtain ⟨he,htail⟩ := List.cons.inj heq
          subst q
          exact ih (child w v p) hqs pre tail htail

theorem expanded_no_stopped_prefix (w : ℝ) (stop : List ℕ → Prop) (n N : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ expanded w stop n v) :
    ¬∃ pre tail : List ℕ,ps=pre++tail ∧ pre∈stopped w stop N v := by
  rintro ⟨pre,tail,he,hstop⟩
  exact expanded_no_lower_stop w stop n v hp pre tail he (stopped_first w stop N v hstop).1

theorem expanded_no_source_stop {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : PrimeHistories.Node)
    (H : Finset ℕ) (mu : ℝ) (n : ℕ) {ps : List ℕ}
    (hp : ps∈expanded w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      n (rootVertex z H (sourcePrimeSet w top) mu)) :
    ¬hasSourceStop hw htop hxi Y Cs eta Clen B b₀ b₁ a z ps := by
  rw [hasSourceStop_iff_original_root hw htop hxi Y Cs eta Clen B b₀ b₁ a z ps H mu]
  exact expanded_no_stopped_prefix w _ n _ _ hp
end NumberTheoryLean.ExpandedNoStop



namespace NumberTheoryLean.PaperRegularStopping
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate SourceNodeCoordinates
open JacobsthalSourceScale PaperMissingPrimeWindow ActualRegularBoxes ActualPrefixClearance
open RegularStoppedEvent RegularStoppedMass PaperRegularTagCapture MovingStopMargins
open ActualBinOwners StrongReferenceTransport LogarithmicBinScale

attribute [local instance] Classical.propDecidable

theorem paper_regular_uncaptured_mass {R Clen Cs eta xi : ℝ} (hR : 3 ≤ R) (hC : 1 ≤ Clen) (hCs : 0 ≤ Cs)
    (heta0 : 0 < eta) (heta : eta < 1/2) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hDelta : 2*Clen*xi ≤ 1) (H : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ rho : ℝ,10 < rho ∧ ∀ K : ℝ,0 < K →
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      ∀ Y : ℕ,Y ≤ ⌊top^2/(Real.log top)^2⌋₊ → ∀ (z : Node) (a : ℕ → ℕ),
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=sourceB (Real.log top) → z.closed=true →
      ∀ Q : (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ) → Finset ℚ,
      (∀ mult ∈ regularBoxes hw htop hxi Clen (sourceB (Real.log top)) R z,(Q mult).card ≤ H) →
      (∀ mult ∈ regularBoxes hw htop hxi Clen (sourceB (Real.log top)) R z,
        ∀ q ∈ Q mult,eligible Y (sourceW (Real.log top)) Cs q) →
      (sourceB (Real.log top))^2 *
        (∑ ps ∈ uncapturedRegular hw htop hxi Y Cs eta Clen (sourceB (Real.log top)) R
          (K*(Real.log (sourceW (Real.log top)))^2)
          (rho*K*(Real.log (sourceW (Real.log top)))^2) a z Q,
          ErdosPrimeInputs.PrimePrefixMass.prefixWeight ps) ≤ epsilon := by
  obtain ⟨rho,hrho,hK⟩ := paper_missing_prime_window_mass R (epsilon/2) hR (by positivity)
  refine ⟨rho,hrho,?_⟩
  intro K hKpos
  obtain ⟨L₀,_hL₀,hmiss⟩ := hK K hKpos
  have hwT := sourceW_tendsto.comp Real.tendsto_log_atTop
  have hBT := sourceB_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [paper_regular_bad_tag_mass hR hC hCs heta0 heta hxi hxi1 hDelta H (epsilon/2) (by positivity),
    hwT.eventually (moving_stop_margins Cs Clen xi hxi (by linarith : 0 < rho) hKpos),
    Real.tendsto_log_atTop.eventually source_scale_eventually,
    Real.tendsto_log_atTop.eventually sourceW_le_sourceB_eventually,
    hBT.eventually_ge_atTop 3,Real.tendsto_log_atTop.eventually_ge_atTop L₀,
    eventually_gt_atTop (1:ℝ)] with top htag hmargin hscale hWB hB3 hL htop1
  obtain ⟨hw,htop,htag⟩ := htag
  obtain ⟨_hw,hlog,hb₀,hCsWin,hsearch,hh,hsmall,hbelow⟩ := hmargin
  refine ⟨hw,htop,?_⟩
  intro Y hY z a hi h199 h23 hz hcut hclosed Q hcard helig
  have hs := (source_node_bounds hscale.2.1 z hi h199 h23 hz hcut).1
  have hg := source_strong_state hB3 z hi h199 hz hcut
  have hcap : (sourceW (Real.log top))^z.cutoff=top := by
    rw [hcut]
    exact (sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans htop1))
  have hroot : (rho*K*(Real.log (sourceW (Real.log top)))^2)/2 < z.cutoff := by
    rw [hcut]
    exact hbelow _ hWB
  have hm := uncaptured_mass_le_exceptions (eta := eta) (K := R) hw htop hxi (by linarith : 0 ≤ Clen) hscale.2.2.2.2
    (source_mesh_clearance_condition hlog hxi.le hC) hb₀ hCsWin hsearch hh hsmall
    Y a z hs hz hg hclosed hcap hroot Q
  have htagmass := htag Y hY z (sourceClass a) hi h199 h23 hz hcut hclosed Q hcard helig
  have hmissmass := hmiss (Real.log top) hL 1 (by norm_num) (by norm_num) z hi h199 h23 hz hcut
  have hm' := mul_le_mul_of_nonneg_left hm (sq_nonneg (sourceB (Real.log top)))
  rw [mul_add] at hm'
  simp only [Function.comp_def] at hm'
  linarith
end NumberTheoryLean.PaperRegularStopping



namespace NumberTheoryLean.ExpandedHardCapture
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualRegularBoxes ActualWordSelection
open StoppedCountAdapters StoppedTraceSets RegularStoppedEvent ExpandedNoStop
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
open ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem expanded_listed_subset_uncaptured {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B K b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node)
    (H : Finset ℕ) (mu : ℝ) (n : ℕ)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (F : Finset (List ℕ))
    (hexp : F ⊆ expanded w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      n (rootVertex z H (sourcePrimeSet w top) mu))
    (hreg : F ⊆ regularWords hw htop hxi Clen B K z)
    (halign : ∀ ps∈F,∃ q∈Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),
      ∀ p∈ps,Cs < primeExponent w p → aligns (sourceClass a) q p) :
    F ⊆ uncapturedRegular hw htop hxi Y Cs eta Clen B K b₀ b₁ a z Q := by
  intro ps hp
  exact Finset.mem_filter.mpr ⟨hreg hp,halign ps hp,
    expanded_no_source_stop hw htop hxi Y Cs eta Clen B b₀ b₁ a z H mu n (hexp hp)⟩

theorem expanded_listed_mass_le {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B K b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node)
    (H : Finset ℕ) (mu : ℝ) (n : ℕ)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (F : Finset (List ℕ))
    (hexp : F ⊆ expanded w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      n (rootVertex z H (sourcePrimeSet w top) mu))
    (hreg : F ⊆ regularWords hw htop hxi Clen B K z)
    (halign : ∀ ps∈F,∃ q∈Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),
      ∀ p∈ps,Cs < primeExponent w p → aligns (sourceClass a) q p) :
    (∑ ps∈F,prefixWeight ps) ≤
      ∑ ps∈uncapturedRegular hw htop hxi Y Cs eta Clen B K b₀ b₁ a z Q,prefixWeight ps :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (expanded_listed_subset_uncaptured hw htop hxi Y Cs eta Clen B K b₀ b₁ a z H mu n Q F hexp hreg halign)
    (fun ps _ _ => prefixWeight_nonneg ps)
end NumberTheoryLean.ExpandedHardCapture


end Erdos970

end OAI
