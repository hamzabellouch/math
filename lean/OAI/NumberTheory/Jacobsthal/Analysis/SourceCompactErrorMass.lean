import OAI.NumberTheory.Jacobsthal.Partitions.GeometricTotalBoxMass
import OAI.NumberTheory.Jacobsthal.Probability.ActualUnlistedEvent

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GlobalCompactTransfer
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate
open JacobsthalSourceScale ActualRegularBoxes ActualBinOwners UniformGeometricRegularMass
open GeometricTotalBoxMass GeometricBoxImages GeometricRegularWords
open ExpandedCompactPartition CountErrorClassification RegularStoppedEvent PaperRegularStopping
open EligibleBoxLists ActualUnlistedEvent FilteredBoxWordMass CanonicalSubsetBox
open StoppedCountVertex StoppedCountAdapters StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosCofactorChoices ErdosSubsetWord ErdosVarianceEligible
open ErdosPrimeInputs.PrimePrefixMass
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem paper_compact_from_local_bounds (K : ℝ) (hK : 3 ≤ K) :
    ∃ Clen₀ Cgeom A : ℝ,1 ≤ Clen₀ ∧ 0 < Cgeom ∧ 0 < A ∧
    ∀ Clen : ℝ,Clen₀ ≤ Clen → ∀ geoErr : ℝ,0 < geoErr →
    ∃ alpha : ℝ,0 < alpha ∧ alpha ≤ 1/400 ∧
    ∀ L Cs eta : ℝ,0 ≤ L → 0 ≤ Cs → 0 < eta → eta < 1/2 →
    ∀ NQ : ℕ,∀ capErr : ℝ,0 < capErr → ∀ xi : ℝ,∀ hxi : 0 < xi,
      xi ≤ 1 → 20*Clen*xi ≤ 1 →
    ∃ rho : ℝ,10 < rho ∧ ∀ Kstop : ℝ,0 < Kstop →
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      ∀ Y : ℕ,Y ≤ ⌊top^2/(Real.log top)^2⌋₊ → ∀ (z : Node) (a : ℕ → ℕ),
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z →
      z.cutoff=sourceB (Real.log top) → z.closed=true →
      ∀ eps tau : ℝ,0 ≤ tau →
      ∀ Qraw : (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ) → Finset ℚ,
      let M := geometricBoxes hw htop hxi Clen (sourceB (Real.log top)) K L alpha (1/100) z
      (∀ m∈M,(Qraw m).card ≤ NQ) →
      (∀ m∈M,(∑ f∈(selections (globalBins (sourceW (Real.log top)) top xi) m).filter
        (unwitnessedSelection hw htop hxi Y Cs Clen (sourceB (Real.log top)) K L alpha (1/100) eps a z (Qraw m)),
        (selectionProduct f:ℝ)⁻¹) ≤ tau*selectionMass (globalBins (sourceW (Real.log top)) top xi) m) →
      let w := sourceW (Real.log top)
      let B := sourceB (Real.log top)
      let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
      let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
      let stop := stopCandidate Y w Cs eta Clen B xi (Kstop*(Real.log w)^2) (rho*Kstop*(Real.log w)^2)
        (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) a z
      B^2*(∑ ps∈badCompactWords w K eps Y small a V0 z
        (expanded w stop (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*V0))),prefixWeight ps)
        ≤ Cgeom*(2*Clen*xi)+geoErr+A*tau+capErr := by
  obtain ⟨A,BA,WA,hA,hBA,hWA,hTotal⟩ := uniform_geometric_box_mass K hK
  obtain ⟨Clen₀,Cgeom,hClen₀,hCgeom,hGeometry⟩ := geometric_defect_uniform_in_L K hK 2 (by norm_num)
    (1/400) (by norm_num) (by norm_num)
  refine ⟨Clen₀,Cgeom,A,hClen₀,hCgeom,hA,?_⟩
  intro Clen hClen geoErr hgeoErr
  have hClen1 : 1 ≤ Clen := hClen₀.trans hClen
  obtain ⟨alpha,halpha,halphaUpper,hL⟩ := hGeometry Clen hClen geoErr hgeoErr
  refine ⟨alpha,halpha,halphaUpper,?_⟩
  intro L Cs eta hL0 hCs heta0 heta NQ capErr hcapErr xi hxi hxi1 h20
  obtain ⟨BG,WG,hBG,hWG,hGeometry⟩ := hL L hL0
  have hbeta : 4*(1/400:ℝ)=1/100 := by norm_num
  rw [hbeta] at hGeometry
  have hDelta : 2*Clen*xi ≤ 1 := by
    have hp : 0 ≤ Clen*xi := mul_nonneg (by linarith) hxi.le
    nlinarith
  obtain ⟨rho,hrho,hCapture⟩ := paper_regular_uncaptured_mass hK hClen1 hCs heta0 heta hxi hxi1 hDelta NQ capErr hcapErr
  refine ⟨rho,hrho,?_⟩
  intro Kstop hKstop
  have hBT := sourceB_tendsto.comp Real.tendsto_log_atTop
  have hWT := sourceW_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [hCapture Kstop hKstop,hBT.eventually_ge_atTop (max BG BA),
    hWT.eventually_ge_atTop (max WG WA),Real.tendsto_log_atTop.eventually source_scale_eventually]
    with top hCapture hB hW hscale
  dsimp only [Function.comp_def] at hB hW
  obtain ⟨hw,htop,hCapture⟩ := hCapture
  refine ⟨hw,htop,?_⟩
  intro Y hY z a hi h199 h23 hz hcut hclosed eps tau htau Qraw
  dsimp only
  intro hcard hLocal
  let w := sourceW (Real.log top)
  let B := sourceB (Real.log top)
  let P := sourcePrimeSet w top
  let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
  let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
  let v := rootVertex z ∅ P ((Y:ℝ)*V0)
  let M := geometricBoxes hw htop hxi Clen B K L alpha (1/100) z
  let Q := eligibleLists (Y:ℝ) w Cs M Qraw
  let b₀ := Kstop*(Real.log w)^2
  let b₁ := rho*Kstop*(Real.log w)^2
  let stop := stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) a z
  let F := badCompactWords w K eps Y small a V0 z (expanded w stop P.card v)
  have hpower : w^B=top := (sourceW_pow_sourceB hw).trans (Real.exp_log ((zero_lt_one.trans hw).trans htop))
  have hRef := bad_compact_reference_data w top K eps Y a z stop P.card V0
  have hGeom := hGeometry B w top ((le_max_left _ _).trans hB) ((le_max_left _ _).trans hW)
    hw htop xi hxi hxi1 h20 hscale.2.2.2.2 z hi h199 h23 hz hcut hclosed hpower F hRef.1 hRef.2
  have hTot := hTotal B w top ((le_max_right _ _).trans hB) ((le_max_right _ _).trans hW)
    hw htop xi Clen hxi hClen1 hscale.2.2.2.2 hDelta z hi h199 h23 hz hcut hclosed hpower L alpha (1/100)
  have hCard := eligibleLists_card (Y:ℝ) w Cs M Qraw NQ hcard
  have hCap := hCapture Y hY z a hi h199 h23 hz hcut hclosed Q
    (fun m _hm => hCard m) (fun m _hm q hq => eligibleLists_eligible (Y:ℝ) w Cs M Qraw m q hq)
  have hBox : ∀ m∈M,selectedWordMass (globalBins w top xi) m
      (unlistedGeometric hw htop hxi Cs Clen B K L alpha (1/100) a z Q F) ≤ tau*selectionMass (globalBins w top xi) m := by
    intro m hm
    exact (selected_unlisted_le_unwitnessed_mass (Cs:=Cs) (C:=Clen) (B:=B) (K:=K) (L:=L)
      (alpha:=alpha) (beta:=1/100) (eps:=eps) hw htop hxi Y M Qraw m hm a z (expanded w stop P.card v)).trans (hLocal m hm)
  have hUnlisted := unlisted_box_transfer hw htop hxi htau a z Q F hTot hBox
  have hSplit := expanded_geometric_mass_split hw htop hxi Y Cs eta Clen B K L alpha (1/100) b₀ b₁ a z
    ∅ ((Y:ℝ)*V0) P.card Q F (fun _ hp => (Finset.mem_filter.mp hp).1)
  have hScaled := mul_le_mul_of_nonneg_left hSplit (sq_nonneg B)
  change B^2*(∑ ps∈F,prefixWeight ps) ≤ Cgeom*(2*Clen*xi)+geoErr+A*tau+capErr
  nlinarith
end NumberTheoryLean.GlobalCompactTransfer



namespace NumberTheoryLean.SourceCompactErrorMass
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate
open GlobalCompactTransfer GeometricBoxImages GeometricRegularWords CountErrorClassification
open StoppedCountVertex StoppedCountAdapters StoppedTraceSets CanonicalSubsetBox
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInverseBoxHeight ErdosCofactorChoices ErdosSubsetWord ErdosVarianceEligible ErdosVarianceFactory
open ErdosPrimeInputs.PrimePrefixMass
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem source_compact_error_mass (K eps budget aStar Cmin : ℝ)
    (hK : 3 ≤ K) (heps : 0 < eps) (hbudget : 0 < budget) (ha : 0 < aStar) (ha1 : aStar ≤ 1) :
    ∃ Clen Cs xi₀ : ℝ,1 ≤ Clen ∧ 0 < Cs ∧ Cmin ≤ Cs ∧ 0 < xi₀ ∧ xi₀ ≤ 1 ∧
    ∀ eta : ℝ,0 < eta → eta < 1/2 → ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ xi₀ →
    ∃ rho : ℝ,10 < rho ∧ ∀ Kstop : ℝ,0 < Kstop →
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW top,∃ htop : sourceW top < top,
      ∀ (z : Node) (a : ℕ → ℕ),z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 →
        Consistent z → z.cutoff=sourceB top → z.closed=true →
        z.gap=Real.log (sourceY top:ℝ)/Real.log (sourceW top)-aStar+2 →
      let w := sourceW top
      let B := sourceB top
      let Y := sourceY top
      let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
      let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
      let stop := stopCandidate Y w Cs eta Clen B xi (Kstop*(Real.log w)^2) (rho*Kstop*(Real.log w)^2)
        (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) a z
      B^2*(∑ ps∈badCompactWords w K eps Y small a V0 z
        (expanded w stop (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*V0))),prefixWeight ps) ≤ budget := by
  obtain ⟨Clen,Cgeom,A,hClen,hCgeom,hA,hGlobal⟩ := paper_compact_from_local_bounds K hK
  have hClen0 : 0 < Clen := by linarith
  have hquarter : 0 < budget/4 := by positivity
  obtain ⟨alpha,halpha,_halphaUpper,hGlobal⟩ := hGlobal Clen (le_refl _) (budget/4) hquarter
  let tau := budget/(4*A)
  have htau : 0 < tau := by dsimp [tau]; positivity
  obtain ⟨Kstar,hKstar,NQ,Cs,hCs,hCsMin,_hCsK,xiF,hxiF,hxiF1,hFactory⟩ :=
    source_raw_box_factory Clen K aStar alpha eps tau Cmin hClen hK ha ha1 halpha heps htau
  let xi₀ := min xiF (min (1/(20*Clen)) (budget/(8*Clen*Cgeom)))
  have hxi₀ : 0 < xi₀ := lt_min hxiF (lt_min (by positivity) (by positivity))
  have hxi₀1 : xi₀ ≤ 1 := (min_le_left _ _).trans hxiF1
  refine ⟨Clen,Cs,xi₀,hClen,hCs,hCsMin,hxi₀,hxi₀1,?_⟩
  intro eta heta0 heta xi hxi hx
  have hxF : xi ≤ xiF := hx.trans (min_le_left _ _)
  have hxi1 : xi ≤ 1 := hx.trans hxi₀1
  have h20 : 20*Clen*xi ≤ 1 := by
    have hh := (le_div_iff₀ (show 0 < 20*Clen by positivity)).mp
      ((hx.trans (min_le_right _ _)).trans (min_le_left _ _))
    nlinarith
  have hGeomBudget : Cgeom*(2*Clen*xi) ≤ budget/4 := by
    have hh := (le_div_iff₀ (show 0 < 8*Clen*Cgeom by positivity)).mp
      ((hx.trans (min_le_right _ _)).trans (min_le_right _ _))
    nlinarith
  have hL : 0 ≤ 2*Kstar+5 := by linarith
  obtain ⟨rho,hrho,hGlobal⟩ := hGlobal (2*Kstar+5) Cs eta hL hCs.le heta0 heta NQ (budget/4) hquarter xi hxi hxi1 h20
  refine ⟨rho,hrho,?_⟩
  intro Kstop hKstop
  filter_upwards [hGlobal Kstop hKstop,hFactory xi hxi hxF] with top hGlobal hFactory
  obtain ⟨hw,htop,hGlobal⟩ := hGlobal
  obtain ⟨_hwF,_htopF,hFactory⟩ := hFactory
  refine ⟨hw,htop,?_⟩
  intro z a hi h199 h23 hz hcut hclosed hroot
  dsimp only
  let M := geometricBoxes hw htop hxi Clen (sourceB top) K (2*Kstar+5) alpha (1/100) z
  have hLists (m : Fin (binCount (sourceW top) top xi) → ℕ) (hm : m∈M) :=
    hFactory z hi h199 hz hcut hclosed hroot a m hm
  have hAll : ∀ m : Fin (binCount (sourceW top) top xi) → ℕ,∃ Q : Finset ℚ,
      Q.card ≤ NQ ∧ (m∈M →
      (∑ f∈(selections (globalBins (sourceW top) top xi) m).filter
        (unwitnessedSelection hw htop hxi (sourceY top) Cs Clen (sourceB top) K (2*Kstar+5) alpha (1/100) eps a z Q),
        (selectionProduct f:ℝ)⁻¹) ≤ tau*selectionMass (globalBins (sourceW top) top xi) m) := by
    intro m
    by_cases hm : m∈M
    · obtain ⟨Q,hcard,hMass⟩ := hLists m hm
      exact ⟨Q,hcard,fun _ => hMass⟩
    · exact ⟨∅,by simp,fun hm' => False.elim (hm hm')⟩
  choose Qraw hCard hLocal using hAll
  have hBound := hGlobal (sourceY top) (le_refl _) z a hi h199 h23 hz hcut hclosed eps tau htau.le Qraw
    (fun m _hm => hCard m) hLocal
  have hTau : A*tau=budget/4 := by dsimp [tau]; field_simp [hA.ne']
  rw [hTau] at hBound
  dsimp only at hBound
  exact hBound.trans (by nlinarith)
end NumberTheoryLean.SourceCompactErrorMass


end Erdos970

end OAI
