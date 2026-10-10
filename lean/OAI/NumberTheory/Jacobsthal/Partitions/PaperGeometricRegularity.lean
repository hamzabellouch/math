import OAI.NumberTheory.Jacobsthal.Estimates.FirstIsolatedPosition
import OAI.NumberTheory.Jacobsthal.Estimates.IsolatedSourceScales
import OAI.NumberTheory.Jacobsthal.Estimates.LargeGapCountErrors
import OAI.NumberTheory.Jacobsthal.Estimates.ReferenceIsolatedExclusion
import OAI.NumberTheory.Jacobsthal.Paths.ExpandedHardCapture
import OAI.NumberTheory.Jacobsthal.Primes.IsolatedRealPrimeRange

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GeometricDefectPartition
open GeometricRegularWords ActualRegularBoxes RepeatedWordEvents NonisolatedWordOccurrence
open PrimeHistories LogarithmicBinLabels
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

attribute [local instance] Classical.propDecidable

theorem geometric_defect_sum {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) (F : Finset (List ℕ)) :
    (∑ ps ∈ F \ geometricWords hw htop hxi C B R L alpha beta z,prefixWeight ps) ≤
      (∑ ps ∈ F \ regularWords hw htop hxi C B R z,prefixWeight ps) +
      (∑ ps ∈ F.filter (compactAdjacentWord w (label (zero_lt_one.trans hw) htop hxi) L z),prefixWeight ps) +
      (∑ ps ∈ F.filter (noIsolatedWord hw htop hxi B alpha beta),prefixWeight ps) := by
  simp only [Finset.sdiff_eq_filter,Finset.sum_filter]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ps _hp
  have hn := prefixWeight_nonneg ps
  by_cases hg : ps ∈ geometricWords hw htop hxi C B R L alpha beta z
  · simp only [hg,not_true_eq_false,ite_false]
    positivity
  · have hf : ps ∉ regularWords hw htop hxi C B R z ∨
        compactAdjacentWord w (label (zero_lt_one.trans hw) htop hxi) L z ps ∨
        noIsolatedWord hw htop hxi B alpha beta ps := by
      by_contra! hh
      exact hg (Finset.mem_filter.mpr ⟨hh.1,hh.2⟩)
    simp only [hg,not_false_eq_true,ite_true]
    split_ifs <;> simp_all
end NumberTheoryLean.GeometricDefectPartition



namespace NumberTheoryLean.GeometricRegularMass
open FinitePathGeometry PrimeHistories ActualRegularBoxes GeometricRegularWords
open RepeatedWordEvents NonisolatedWordOccurrence ReferenceAdmission GeometricDefectPartition
open BasicRegularMass ReferenceRepeatedExclusion ReferenceIsolatedExclusion
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem geometric_regular_defect_mass (R : ℝ) (hR : 3 ≤ R) (D : ℝ) (hD : 0 < D)
    (L : ℝ) (hL : 0 ≤ L) (theta : ℝ) (htheta : 0 < theta) (htheta1 : theta ≤ 1/2) :
    ∃ Clen₀ C : ℝ,1 ≤ Clen₀ ∧ 0 < C ∧ ∀ Clen : ℝ,Clen₀ ≤ Clen → ∀ eps : ℝ,0 < eps →
      ∃ alpha B₀ w₀ : ℝ,0 < alpha ∧ alpha ≤ theta ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
      ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ hw : 1 < w,∀ htop : w < top,
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → 20*Clen*xi ≤ 1 → Real.log B ≤ D*Real.log w →
      ∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 →
      PrimeBinMembership.Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ F : Finset (List ℕ),F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps ∈ F,(terminal w z ps).gap ≤ R) →
      B^2*(∑ ps ∈ F \ geometricWords hw htop hxi Clen B R L alpha (4*theta) z,prefixWeight ps) ≤ C*(2*Clen*xi)+eps := by
  obtain ⟨Clen₀,C,hClen₀,hC,hBasic⟩ := basic_regular_defect_mass R hR D hD
  refine ⟨Clen₀,C,hClen₀,hC,?_⟩
  intro Clen hClen eps heps
  have he : 0 < eps/3 := by positivity
  obtain ⟨BA,WA,hBA,hWA,hBasic⟩ := hBasic Clen hClen (eps/3) he
  obtain ⟨BB,WB,hBB,hWB,hRepeat⟩ := uniform_reference_repeated_mass R hR D hD L hL (eps/3) he
  obtain ⟨alpha,BC,WC,ha,hath,hBC,hWC,hIsolated⟩ := uniform_reference_nonisolated_mass R hR D hD theta htheta htheta1 (eps/3) he
  refine ⟨alpha,max BA (max BB BC),max WA (max WB WC),ha,hath,hBA.trans (le_max_left _ _),hWA.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ hw htop xi hxi hxi1 hsmall hcomp z hi h199 h23 hz hcut hclosed hcap F hF hg
  have hBa : BA ≤ B := (le_max_left _ _).trans hB
  have hBb : BB ≤ B := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hB
  have hBc : BC ≤ B := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hB
  have hWa : WA ≤ w := (le_max_left _ _).trans hw₀
  have hWb : WB ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw₀
  have hWc : WC ≤ w := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hw₀
  have hb := hBasic B w top hBa hWa hw htop xi hxi hxi1 hsmall hcomp z hi h199 h23 hz hcut hclosed hcap F hF hg
  have hr := hRepeat B w top hBb hWb hw htop xi hxi hxi1 hcomp z hi h199 h23 hz hcut hclosed hcap
    (F.filter (compactAdjacentWord w (label (zero_lt_one.trans hw) htop hxi) L z))
    (fun ps hp => hF (Finset.mem_filter.mp hp).1)
    (fun ps hp => ⟨hg ps (Finset.mem_filter.mp hp).1,Or.inr (Finset.mem_filter.mp hp).2⟩)
  have hi' := hIsolated B w top hBc hWc hw htop xi hxi hxi1 hcomp z hi h199 h23 hz hcut hclosed hcap
    (F.filter (noIsolatedWord hw htop hxi B alpha (4*theta)))
    (fun ps hp => hF (Finset.mem_filter.mp hp).1)
    (fun ps hp => ⟨hg ps (Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2⟩)
  have hp := mul_le_mul_of_nonneg_left (geometric_defect_sum (C:=Clen) (B:=B) (R:=R) (L:=L) (alpha:=alpha)
    (beta:=4*theta) hw htop hxi z F) (sq_nonneg B)
  nlinarith
end NumberTheoryLean.GeometricRegularMass



namespace NumberTheoryLean.UniformGeometricRegularMass
open FinitePathGeometry PrimeHistories ActualRegularBoxes GeometricRegularWords
open RepeatedWordEvents NonisolatedWordOccurrence ReferenceAdmission GeometricDefectPartition
open BasicRegularMass ReferenceRepeatedExclusion ReferenceIsolatedExclusion
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem geometric_defect_uniform_in_L (R : ℝ) (hR : 3 ≤ R) (D : ℝ) (hD : 0 < D)
    (theta : ℝ) (htheta : 0 < theta) (htheta1 : theta ≤ 1/2) :
    ∃ Clen₀ C : ℝ,1 ≤ Clen₀ ∧ 0 < C ∧ ∀ Clen : ℝ,Clen₀ ≤ Clen → ∀ eps : ℝ,0 < eps →
      ∃ alpha : ℝ,0 < alpha ∧ alpha ≤ theta ∧ ∀ L : ℝ,0 ≤ L →
      ∃ B₀ w₀ : ℝ,3 ≤ B₀ ∧ 1 < w₀ ∧
      ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ hw : 1 < w,∀ htop : w < top,
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → 20*Clen*xi ≤ 1 → Real.log B ≤ D*Real.log w →
      ∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 →
      PrimeBinMembership.Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ F : Finset (List ℕ),F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps ∈ F,(terminal w z ps).gap ≤ R) →
      B^2*(∑ ps ∈ F \ geometricWords hw htop hxi Clen B R L alpha (4*theta) z,prefixWeight ps) ≤ C*(2*Clen*xi)+eps := by
  obtain ⟨Clen₀,C,hClen₀,hC,hBasic⟩ := basic_regular_defect_mass R hR D hD
  refine ⟨Clen₀,C,hClen₀,hC,?_⟩
  intro Clen hClen eps heps
  have he : 0 < eps/3 := by positivity
  obtain ⟨BA,WA,hBA,hWA,hBasic⟩ := hBasic Clen hClen (eps/3) he
  obtain ⟨alpha,BC,WC,ha,hath,hBC,hWC,hIsolated⟩ := uniform_reference_nonisolated_mass R hR D hD theta htheta htheta1 (eps/3) he
  refine ⟨alpha,ha,hath,?_⟩
  intro L hL
  obtain ⟨BB,WB,hBB,hWB,hRepeat⟩ := uniform_reference_repeated_mass R hR D hD L hL (eps/3) he
  refine ⟨max BA (max BB BC),max WA (max WB WC),hBA.trans (le_max_left _ _),hWA.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ hw htop xi hxi hxi1 hsmall hcomp z hi h199 h23 hz hcut hclosed hcap F hF hg
  have hBa : BA ≤ B := (le_max_left _ _).trans hB
  have hBb : BB ≤ B := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hB
  have hBc : BC ≤ B := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hB
  have hWa : WA ≤ w := (le_max_left _ _).trans hw₀
  have hWb : WB ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw₀
  have hWc : WC ≤ w := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hw₀
  have hb := hBasic B w top hBa hWa hw htop xi hxi hxi1 hsmall hcomp z hi h199 h23 hz hcut hclosed hcap F hF hg
  have hr := hRepeat B w top hBb hWb hw htop xi hxi hxi1 hcomp z hi h199 h23 hz hcut hclosed hcap
    (F.filter (compactAdjacentWord w (label (zero_lt_one.trans hw) htop hxi) L z))
    (fun ps hp => hF (Finset.mem_filter.mp hp).1)
    (fun ps hp => ⟨hg ps (Finset.mem_filter.mp hp).1,Or.inr (Finset.mem_filter.mp hp).2⟩)
  have hi' := hIsolated B w top hBc hWc hw htop xi hxi hxi1 hcomp z hi h199 h23 hz hcut hclosed hcap
    (F.filter (noIsolatedWord hw htop hxi B alpha (4*theta)))
    (fun ps hp => hF (Finset.mem_filter.mp hp).1)
    (fun ps hp => ⟨hg ps (Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2⟩)
  have hp := mul_le_mul_of_nonneg_left (geometric_defect_sum (C:=Clen) (B:=B) (R:=R) (L:=L) (alpha:=alpha)
    (beta:=4*theta) hw htop hxi z F) (sq_nonneg B)
  nlinarith
end NumberTheoryLean.UniformGeometricRegularMass



namespace NumberTheoryLean.ExpandedCompactPartition
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualRegularBoxes ActualWordSelection
open StoppedCountAdapters StoppedTraceSets ExpandedHardCapture RegularStoppedEvent
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open GeometricRegularWords CountErrorClassification LiteralCountErrorLedger
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.PrimePrefixTail ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def listedWord {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Cs : ℝ) (a : ℕ → ℕ)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (ps : List ℕ) : Prop :=
  ∃ q∈Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),
    ∀ p∈ps,Cs < primeExponent w p → aligns (sourceClass a) q p

noncomputable def unlistedGeometric {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Cs C B K L alpha beta : ℝ)
    (a : ℕ → ℕ) (z : Node) (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (F : Finset (List ℕ)) : Finset (List ℕ) :=
  (F∩geometricWords hw htop hxi C B K L alpha beta z).filter (fun ps => ¬listedWord hw htop hxi Cs a Q ps)

theorem expanded_geometric_mass_split {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta C B K L alpha beta b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node)
    (H : Finset ℕ) (mu : ℝ) (n : ℕ)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (F : Finset (List ℕ))
    (hexp : F ⊆ expanded w
      (stopCandidate Y w Cs eta C B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      n (rootVertex z H (sourcePrimeSet w top) mu)) :
    (∑ ps∈F,prefixWeight ps) ≤
      (∑ ps∈F\geometricWords hw htop hxi C B K L alpha beta z,prefixWeight ps)+
      (∑ ps∈unlistedGeometric hw htop hxi Cs C B K L alpha beta a z Q F,prefixWeight ps)+
      ∑ ps∈uncapturedRegular hw htop hxi Y Cs eta C B K b₀ b₁ a z Q,prefixWeight ps := by
  let G := geometricWords hw htop hxi C B K L alpha beta z
  let T := (F∩G).filter (listedWord hw htop hxi Cs a Q)
  have hTexp : T ⊆ expanded w
      (stopCandidate Y w Cs eta C B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      n (rootVertex z H (sourcePrimeSet w top) mu) :=
    fun _ hp => hexp (Finset.mem_inter.mp (Finset.mem_filter.mp hp).1).1
  have hTreg : T ⊆ regularWords hw htop hxi C B K z :=
    fun _ hp => (Finset.mem_filter.mp (Finset.mem_inter.mp (Finset.mem_filter.mp hp).1).2).1
  have hTalign : ∀ ps∈T,∃ q∈Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),
      ∀ p∈ps,Cs < primeExponent w p → aligns (sourceClass a) q p :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  have hbound := expanded_listed_mass_le hw htop hxi Y Cs eta C B K b₀ b₁ a z H mu n Q T hTexp hTreg hTalign
  have hsplit := Finset.sum_filter_add_sum_filter_not (F∩G) (listedWord hw htop hxi Cs a Q) prefixWeight
  have hgeo := Finset.sum_filter_add_sum_filter_not F (fun ps => ps∈G) prefixWeight
  simp only [Finset.filter_mem_eq_inter,← Finset.sdiff_eq_filter] at hgeo
  change (∑ ps∈F,prefixWeight ps) ≤ (∑ ps∈F\G,prefixWeight ps)+
    (∑ ps∈(F∩G).filter (fun ps => ¬listedWord hw htop hxi Cs a Q ps),prefixWeight ps)+_
  dsimp only [T] at hbound
  linarith

theorem bad_compact_reference_data (w top K eps : ℝ) (Y : ℕ) (a : ℕ → ℕ)
    (z : Node) (stop : List ℕ → Prop) (n : ℕ) (V0 : ℝ) :
    let F := badCompactWords w K eps Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a V0 z
      (expanded w stop n (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*V0)))
    F ⊆ ReferenceAdmission.referencePrefixes w (sourcePrimeSet w top) z.side z.gap ∧
      ∀ ps∈F,(terminal w z ps).gap ≤ K := by
  dsimp only
  exact ⟨fun _ hp => expanded_reference_subset w _ z _ stop n (Finset.mem_filter.mp hp).1,
    fun _ hp => (Finset.mem_filter.mp hp).2.1⟩
end NumberTheoryLean.ExpandedCompactPartition



namespace NumberTheoryLean.PaperGeometricRegularity
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open JacobsthalSourceScale GeometricRegularWords GeometricRegularMass IsolatedSourceScales
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinEndpoints LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass
open scoped Topology

attribute [local instance] Classical.propDecidable

theorem paper_geometric_defect_mass (R : ℝ) (hR : 3 ≤ R) (L : ℝ) (hL : 0 ≤ L) :
    ∃ Clen₀ C : ℝ,1 ≤ Clen₀ ∧ 0 < C ∧ ∀ Clen : ℝ,Clen₀ ≤ Clen → ∀ eps : ℝ,0 < eps →
      ∃ alpha : ℝ,0 < alpha ∧ alpha ≤ 1/400 ∧ ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → 20*Clen*xi ≤ 1 →
      ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      (sourceW (Real.log top))^((1/4:ℝ)) ≤ alpha*sourceB (Real.log top) ∧
      ∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 →
      Consistent z → z.cutoff=sourceB (Real.log top) → z.closed=true →
      ∀ F : Finset (List ℕ),F ⊆ ReferenceAdmission.referencePrefixes (sourceW (Real.log top))
          (sourcePrimeSet (sourceW (Real.log top)) top) z.side z.gap →
      (∀ ps ∈ F,(terminal (sourceW (Real.log top)) z ps).gap ≤ R) →
      (sourceB (Real.log top))^2*(∑ ps ∈ F \ geometricWords hw htop hxi Clen (sourceB (Real.log top)) R L alpha (1/100) z,
        prefixWeight ps) ≤ C*(2*Clen*xi)+eps := by
  obtain ⟨Clen₀,C,hClen₀,hC,hBound⟩ := geometric_regular_defect_mass R hR 2 (by norm_num) L hL (1/400) (by norm_num) (by norm_num)
  refine ⟨Clen₀,C,hClen₀,hC,?_⟩
  intro Clen hClen eps heps
  obtain ⟨alpha,B₀,w₀,ha,hath,hB₀,hw₀,hMass⟩ := hBound Clen hClen eps heps
  refine ⟨alpha,ha,hath,?_⟩
  intro xi hxi hxi1 hsmall
  have hwT := sourceW_tendsto.comp Real.tendsto_log_atTop
  have hBT := sourceB_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [hwT.eventually_ge_atTop w₀,hBT.eventually_ge_atTop B₀,
    Real.tendsto_log_atTop.eventually source_scale_eventually,
    Real.tendsto_log_atTop.eventually (source_isolated_search_scale ha),
    eventually_gt_atTop (1:ℝ)] with top hwB hBB hscale hsearch htop1
  have hw : 1 < sourceW (Real.log top) := hscale.1
  have htop : sourceW (Real.log top) < top := by
    have hpow : (sourceW (Real.log top))^(sourceB (Real.log top))=top :=
      (sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans htop1))
    have hB3 : 3 ≤ sourceB (Real.log top) := hB₀.trans hBB
    have hh := Real.rpow_lt_rpow_of_exponent_lt hw (show (1:ℝ)<sourceB (Real.log top) by linarith)
    simpa only [Real.rpow_one,hpow] using hh
  refine ⟨hw,htop,hsearch,?_⟩
  intro z hi h199 h23 hc hcut hclosed F hF hg
  have hcap : (sourceW (Real.log top))^(sourceB (Real.log top))=top :=
    (sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans htop1))
  have hh := hMass (sourceB (Real.log top)) (sourceW (Real.log top)) top hBB hwB hw htop xi hxi hxi1 hsmall
    hscale.2.2.2.2 z hi h199 h23 hc hcut hclosed hcap F hF hg
  norm_num only [show (4:ℝ)*(1/400)=1/100 by norm_num] at hh
  exact hh
end NumberTheoryLean.PaperGeometricRegularity


end Erdos970

end OAI
