import OAI.NumberTheory.Jacobsthal.Estimates.WeightedTwoExceptions
import OAI.NumberTheory.Jacobsthal.Paths.OutsideExceptionsWitness

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GeometricCandidateCount
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
open SafeSubsetBoxGeometry GeometricBoxImages BoundedCandidateCount
open LogarithmicBinScale LogarithmicBinLabels

theorem geometric_candidate_card {w top xi B C K L alpha beta a M X : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 1 ≤ C) (hlog : 1 ≤ Real.log w)
    (hcomp : Real.log B ≤ 2*Real.log w) (hB : 3 ≤ B) (ha0 : 0 ≤ a)
    (Y : ℕ) (hY : 0 < Y) (z : Node) (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hi : z.side=.even) (h199 : 199/100 ≤ z.ratio) (hz : Consistent z) (hcut : z.cutoff=B) (hclosed : z.closed=true)
    (hpower : w^B=top) (m : Fin (binCount w top xi) → ℕ)
    (hm : m ∈ geometricBoxes hw htop hxi C B K L alpha beta z) :
    (candidateBins w top xi Y m M X).card ≤ ⌈M⌉₊ := by
  have hsmall : 2*(xi/Real.log w) ≤ 6*(2*C*xi) := by
    have hh := div_le_self hxi.le hlog
    nlinarith
  have hA := geometric_box_anchor hw htop hxi (by linarith : 0 ≤ C) hcomp hsmall z m hm
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB z hi h199 hz hcut
  have hcap : w^z.cutoff=top := by rwa [hcut]
  exact candidate_bins_card_le hw htop hxi (by linarith) hcomp ha0 Y hY z hroot hs hz hg hclosed hcap m hA
end NumberTheoryLean.GeometricCandidateCount



namespace NumberTheoryLean.GeometricRangeCandidateUnion
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open GeometricBoxImages GeometricInverseGeometry BoundedEdgeBins ParentCofactorChoices
open JacobsthalSourceScale IsolatedSourceScales SourceNodeCoordinates
open GeometricRangeInverse GeometricCandidateCount CandidateExceptionMass BoundedCandidateCount
open ActualInverseFullBoxMass BoxWitnessFactorization CanonicalSubsetBox IsolatedPowerOrdering ErdosInverseSampleCost
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseBoxApplication
open LogarithmicBinScale LogarithmicBinEndpoints
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem geometric_range_candidate_union (C Kstar aStar alpha delta sigma : ℝ)
    (hC : 1 ≤ C) (hKstar : 0 ≤ Kstar) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (halpha : 0 < alpha) (hd : 0 < delta) (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1) :
    ∃ cp : ℝ,0 < cp ∧ ∃ F : ℕ,∃ xi₀ : ℝ,0 < xi₀ ∧ xi₀ ≤ 1 ∧
    ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ xi₀ → ∀ᶠ top : ℝ in atTop,
      ∃ hw : 1 < ErdosInverseBoxHeight.sourceW top,∃ htop : ErdosInverseBoxHeight.sourceW top < top,
      ∀ R L : ℝ,∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → Consistent z →
        z.cutoff=ErdosInverseBoxHeight.sourceB top → z.closed=true →
        z.gap=Real.log (ErdosInverseBoxHeight.sourceY top:ℝ)/Real.log (ErdosInverseBoxHeight.sourceW top)-aStar+2 →
      ∀ m ∈ geometricBoxes hw htop hxi C (ErdosInverseBoxHeight.sourceB top) R L alpha (1/100) z,
      ∃ i : Fin (binCount (ErdosInverseBoxHeight.sourceW top) top xi),m i=1 ∧
      top^alpha ≤ lower (ErdosInverseBoxHeight.sourceW top) top xi i ∧
      lower (ErdosInverseBoxHeight.sourceW top) top xi i ≤ top^((1:ℝ)/100) ∧
      (∀ j : Fin (binCount (ErdosInverseBoxHeight.sourceW top) top xi),
        boundedEdgeBin (ErdosInverseBoxHeight.sourceW top) top xi (ErdosInverseBoxHeight.sourceY top) m
          (2*Kstar+3) (2*Kstar+3) j → ∀ residue : ℕ → ℕ,
        j < i ∧ m j=1 ∧
        let cm := parentCofactorMultiplicity m i j
        let w := ErdosInverseBoxHeight.sourceW top
        SourceInverseConclusion (ErdosInverseBoxHeight.sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊)
          residue delta (SmallSieveFinite.smallEuler ⌊w⌋₊) (cofactorScale top xi cm)
          (lower w top xi i) (ErdosInverseBoxHeight.sourceZ top) cp sigma F
          (actualBins top xi i) (cofactorChoices (actualBins top xi) cm) (actualBins top xi j) ∧
        selectionWitnessMass (actualBins top xi) m i j
          (actualWitness (ErdosInverseBoxHeight.sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue delta
            (SmallSieveFinite.smallEuler ⌊w⌋₊) (actualBins top xi i) (cofactorScale top xi cm)
            (lower w top xi i) (ErdosInverseBoxHeight.sourceZ top) cp) ≤ sigma*selectionMass (actualBins top xi) m ) ∧ ∀ residue : ℕ → ℕ,
        someWitnessMass (actualBins top xi) m i
          (candidateBins (ErdosInverseBoxHeight.sourceW top) top xi (ErdosInverseBoxHeight.sourceY top) m (2*Kstar+3) (2*Kstar+3))
          (fun j => actualWitness (ErdosInverseBoxHeight.sourceY top)
            (LargePrimeDeletion.cutoffPrimes ⌊ErdosInverseBoxHeight.sourceW top⌋₊) residue delta
            (SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW top⌋₊) (actualBins top xi i)
            (cofactorScale top xi (parentCofactorMultiplicity m i j)) (lower (ErdosInverseBoxHeight.sourceW top) top xi i)
            (ErdosInverseBoxHeight.sourceZ top) cp) ≤ (⌈2*Kstar+3⌉₊:ℝ)*sigma*selectionMass (actualBins top xi) m := by
  obtain ⟨cp,hcp,F,xi₀,hxi₀,hxi₀1,hCore⟩ := geometric_range_inverse C Kstar aStar alpha delta sigma
    hC hKstar ha ha1 halpha hd hsigma hsigma1
  refine ⟨cp,hcp,F,xi₀,hxi₀,hxi₀1,?_⟩
  intro xi hxi hx
  have hBT := sourceB_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [hCore xi hxi hx,hBT.eventually_ge_atTop 3,
    Real.tendsto_log_atTop.eventually source_scale_eventually,ErdosInverseBoxHeight.source_B_bounds]
    with top hCore hB3 hscale hbounds
  obtain ⟨hw,htop,hData⟩ := hCore
  change 3 ≤ ErdosInverseBoxHeight.sourceB top at hB3
  have hlog : 1 ≤ Real.log (ErdosInverseBoxHeight.sourceW top) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hbounds.1
    simpa only [Real.log_exp] using hh
  have hpow : (ErdosInverseBoxHeight.sourceW top)^(ErdosInverseBoxHeight.sourceB top)=top :=
    (sourceW_pow_sourceB hw).trans (Real.exp_log ((zero_lt_one.trans hw).trans htop))
  refine ⟨hw,htop,?_⟩
  intro R L z hi h199 hz hcut hclosed hroot m hm
  obtain ⟨i,hmi,hilo,hihi,hStep⟩ := hData R L z hi h199 hz hcut hclosed hroot m hm
  refine ⟨i,hmi,hilo,hihi,hStep,?_⟩
  intro residue
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hY : 0 < ErdosInverseBoxHeight.sourceY top := by
    by_contra! hn
    have hzero : ErdosInverseBoxHeight.sourceY top=0 := by omega
    rw [hzero,Nat.cast_zero,Real.log_zero,zero_div] at hroot
    have hg := node_gap_eq hs hz hcut
    nlinarith
  have hCard := geometric_candidate_card (M:=2*Kstar+3) (X:=2*Kstar+3) hw htop hxi hC hlog hscale.2.2.2.2
    hB3 ha.le (ErdosInverseBoxHeight.sourceY top) hY z hroot hi h199 hz hcut hclosed hpow m hm
  apply some_witness_mass_card_bound _ _ _ _ _ sigma hsigma.le _ hCard
  intro j hj
  exact (hStep j (Finset.mem_filter.mp hj).2 residue).2.2.2
end NumberTheoryLean.GeometricRangeCandidateUnion



namespace ErdosVarianceEligible
open NumberTheoryLean PrimeHistories GeometricRegularWords ActualCountErrorEdges ErdosCofactorChoices ErdosSubsetWord
  LogarithmicBinScale

def unwitnessedSelection {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs C B K L alpha beta eps : ℝ) (residue : ℕ → ℕ) (z : Node) (Q : Finset ℚ)
    (f : Fin (binCount w top xi) → Finset ℕ) : Prop :=
  descendingWord f ∈ geometricWords hw htop hxi C B K L alpha beta z ∧
    eps < |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) (descendingWord f)| ∧
    ¬eligibleWordWitness Y w Cs residue Q (descendingWord f)

end ErdosVarianceEligible



open _root_.Filter
namespace ErdosVarianceFactory
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
  SafeSubsetBoxGeometry GeometricBoxImages GeometricCandidateCount GeometricRangeCandidateUnion
  GeometricRegularWords BoundedEdgeBins BoundedCandidateCount CandidateExceptionMass
  ParentCofactorChoices ParentTailPartition SingletonBinSelection TwoPrimeObservableSum CanonicalSubsetBox
  RawBoxRationalWitness ErdosCofactorChoices ErdosSubsetWord ErdosVarianceWeighted ErdosVarianceEligible
  ErdosInverseBoxHeight ErdosInverseEuler ErdosInverseCells ErdosInverseCounts ErdosInverseAlignment
  ErdosInverseBoxApplication ErdosInverseSampleCost
  LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinPartition
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_raw_box_factory (C K aStar alpha eps tau Cmin : ℝ)
    (hC : 1 ≤ C) (hK : 3 ≤ K) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (halpha : 0 < alpha) (heps : 0 < eps) (htau : 0 < tau) :
    ∃ Kstar : ℝ,K+10 < Kstar ∧ ∃ NQ : ℕ,∃ Cs : ℝ,0 < Cs ∧ Cmin ≤ Cs ∧ 2*Kstar+4 ≤ Cs ∧
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
    ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ xi0 → ∀ᶠ top : ℝ in atTop,
      ∃ hw : 1 < sourceW top,∃ htop : sourceW top < top,
      ∀ z : Node,z.side = .even → 199/100 ≤ z.ratio → Consistent z →
        z.cutoff = sourceB top → z.closed = true →
        z.gap = Real.log (sourceY top : ℝ)/Real.log (sourceW top)-aStar+2 →
      ∀ residue : ℕ → ℕ,
      ∀ m ∈ geometricBoxes hw htop hxi C (sourceB top) K (2*Kstar+5) alpha (1/100) z,
      ∃ Q : Finset ℚ,Q.card ≤ NQ ∧
        (∑ f ∈ (selections (globalBins (sourceW top) top xi) m).filter
          (unwitnessedSelection hw htop hxi (sourceY top) Cs C (sourceB top) K (2*Kstar+5) alpha (1/100) eps residue z Q),
          (selectionProduct f : ℝ)⁻¹) ≤ tau*selectionMass (globalBins (sourceW top) top xi) m := by
  obtain ⟨Kstar,B0,w0,hKs,hB0,_hw0,hrecent⟩ := geometric_selection_recent_witness K eps hK heps
  have hKs0 : 0 ≤ Kstar := by linarith
  let M := 2*Kstar+3
  have hM : 0 ≤ M := by dsimp [M];linarith
  have hH : 0 < ⌈2*Kstar+10⌉₊ := by
    have hh := Nat.le_ceil (2*Kstar+10)
    by_contra! hn
    have he : ⌈2*Kstar+10⌉₊ = 0 := by omega
    rw [he,Nat.cast_zero] at hh
    linarith
  let delta := eps/(4*(⌈2*Kstar+10⌉₊ : ℝ))
  have hdelta : 0 < delta := by dsimp [delta];positivity
  let sigma := min 1 (tau/(2*((⌈M⌉₊ : ℝ)+1)))
  have hsigma : 0 < sigma := lt_min zero_lt_one (by positivity)
  have hsigma1 : sigma ≤ 1 := min_le_left _ _
  have hsigmaBudget : (⌈M⌉₊ : ℝ)*sigma ≤ tau/2 := by
    have hh := (le_div_iff₀ (show 0 < 2*((⌈M⌉₊ : ℝ)+1) by positivity)).mp
      (min_le_right (1 : ℝ) (tau/(2*((⌈M⌉₊ : ℝ)+1))))
    change sigma*(2*((⌈M⌉₊ : ℝ)+1)) ≤ tau at hh
    nlinarith
  obtain ⟨cp,_hcp,F,xiI,hxiI,hxiI1,hInverse⟩ := geometric_range_candidate_union C Kstar aStar alpha delta sigma
    hC hKs0 ha ha1 halpha hdelta hsigma hsigma1
  let NQ := ⌈M⌉₊*F
  let requiredCs := max Cmin (2*Kstar+4)
  obtain ⟨Cs,hCs,hCsReq,xiH,hxiH,_hxiH1,hHard⟩ :=
    geometric_selection_hard_mass C aStar alpha eps (tau/2) requiredCs NQ hC ha halpha heps (by positivity)
  have hCsMin : Cmin ≤ Cs := (le_max_left _ _).trans hCsReq
  have hCsK : 2*Kstar+4 ≤ Cs := (le_max_right _ _).trans hCsReq
  have hCpos : 0 < C := by linarith
  let xi0 := min xiI (min xiH (1/(2*C)))
  have hxi0 : 0 < xi0 := lt_min hxiI (lt_min hxiH (by positivity))
  have hxi01 : xi0 ≤ 1 := (min_le_left _ _).trans hxiI1
  refine ⟨Kstar,hKs,NQ,Cs,hCs,hCsMin,hCsK,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxiInv : xi ≤ xiI := hxib.trans (min_le_left _ _)
  have hxiHard : xi ≤ xiH := (hxib.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hxiDelta : xi ≤ 1/(2*C) := (hxib.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hDelta : 2*C*xi ≤ 1 := by
    have hh := (le_div_iff₀ (show 0 < 2*C by positivity)).mp hxiDelta
    nlinarith
  have hxi1 := hxib.trans hxi01
  have hBT := JacobsthalSourceScale.sourceB_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [hInverse xi hxi hxiInv,hHard xi hxi hxiHard,
    outside_exceptions_eligible_word C M (by linarith : 0 ≤ C) hM,
    hBT.eventually_ge_atTop B0,sourceW_tendsto_atTop.eventually_ge_atTop w0,
    Real.tendsto_log_atTop.eventually JacobsthalSourceScale.source_scale_eventually,source_B_bounds]
    with top hInvTop hHardTop hOutside hB hwMin hscale hWbounds
  obtain ⟨hw,htop,hInvData⟩ := hInvTop
  obtain ⟨_hwH,_htopH,hHardData⟩ := hHardTop
  have hB3 : 3 ≤ sourceB top := hB0.trans hB
  have hcomp : Real.log (sourceB top) ≤ 2*Real.log (sourceW top) := hscale.2.2.2.2
  have hlog : 1 ≤ Real.log (sourceW top) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hWbounds.1
  have hsmall : 2*(xi/Real.log (sourceW top)) ≤ 6*(2*C*xi) := by
    have hh := div_le_self hxi.le hlog
    nlinarith
  have hpower : (sourceW top)^(sourceB top) = top :=
    (JacobsthalSourceScale.sourceW_pow_sourceB hw).trans (Real.exp_log ((zero_lt_one.trans hw).trans htop))
  refine ⟨hw,htop,?_⟩
  intro z heven h199 hz hcut hclosed hroot residue m hm
  have hs : Valid z.side z.ratio := by rw [heven];change 198/100 ≤ z.ratio;linarith
  have hStrong := source_strong_state hB3 z heven h199 hz hcut
  have hY : 0 < sourceY top := by
    by_contra! hn
    have hzero : sourceY top = 0 := by omega
    rw [hzero,Nat.cast_zero,Real.log_zero,zero_div] at hroot
    linarith [hStrong.1]
  have hcap : (sourceW top)^z.cutoff = top := by rwa [hcut]
  have hanchor := geometric_box_anchor hw htop hxi (by linarith : 0 ≤ C) hcomp hsmall z m hm
  obtain ⟨i,hmi,hRi,_hRiUpper,hStep,hInvMass⟩ :=
    hInvData K (2*Kstar+5) z heven h199 hz hcut hclosed hroot m hm
  let P := globalBins (sourceW top) top xi
  let J := candidateBins (sourceW top) top xi (sourceY top) m M M
  let S := fun j => cofactorScale top xi (parentCofactorMultiplicity m i j)
  let R := lower (sourceW top) top xi i
  let Q := rawBoxList P i J residue S R (sourceZ top) cp
  have hJ : ∀ j ∈ J,boundedEdgeBin (sourceW top) top xi (sourceY top) m M M j ∧ j < i := by
    intro j hj
    have hb := (Finset.mem_filter.mp hj).2
    exact ⟨hb,(hStep j hb residue).1⟩
  have hInv : ∀ j ∈ J,SourceInverseConclusion (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊)
      residue delta (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) (S j) R (sourceZ top) cp sigma F
      (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j) :=
    fun j hj => (hStep j (hJ j hj).1 residue).2.2.1
  have hJcard : J.card ≤ ⌈M⌉₊ := geometric_candidate_card hw htop hxi hC hlog hcomp hB3 ha.le
    (sourceY top) hY z hroot heven h199 hz hcut hclosed hpower m hm
  have hQcard : Q.card ≤ NQ :=
    (raw_box_list_card P m i J (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊)
      residue delta (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) S R (sourceZ top) cp sigma F hInv).trans
      (Nat.mul_le_mul_right F hJcard)
  refine ⟨Q,hQcard,?_⟩
  let EInv := fun f => ∃ j ∈ J,actualWitness (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊) residue delta
    (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) (P i) (S j) R (sourceZ top) cp
      (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)
  let EHard := hardSelection Q top R (width (sourceW top) top xi i) residue i Cs eps
  let E := unwitnessedSelection hw htop hxi (sourceY top) Cs C (sourceB top) K (2*Kstar+5) alpha (1/100) eps residue z Q
  have hsub : ∀ f ∈ selections P m,E f → EInv f ∨ EHard f := by
    intro f hf hE
    by_cases hEI : EInv f
    · exact Or.inl hEI
    by_cases hEH : EHard f
    · exact Or.inr hEH
    have hgeom := hE.1
    have hbad := hE.2.1
    obtain ⟨j,hjb,hEdge⟩ := hrecent (sourceB top) (sourceW top) top hB hwMin hw htop xi hxi C hC hcomp
      aStar alpha (1/100) ha.le ha1 (sourceY top) hY z hroot heven h199 hz hcut hclosed hpower
      residue m f hf hgeom hbad
    have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjb⟩
    have hWitness := hEdge i hmi (hJ j hjJ).2
    have hEligible := hOutside xi hxi hxi1 hDelta hw htop K aStar M ha.le z hY hroot hs hz hStrong hclosed hcap
      m hanchor f hf i hmi J hJ residue delta cp sigma Cs eps F hInv ⟨j,hjJ,hWitness⟩ hbad hEI hEH
    exact False.elim (hE.2.2 hEligible)
  have hInvBound : (∑ f ∈ (selections P m).filter EInv,(selectionProduct f : ℝ)⁻¹) ≤
      (⌈M⌉₊ : ℝ)*sigma*selectionMass P m := hInvMass residue
  have hHardBound : (∑ f ∈ (selections P m).filter EHard,(selectionProduct f : ℝ)⁻¹) ≤
      (tau/2)*selectionMass P m :=
    hHardData K (2*Kstar+5) z heven h199 hz hcut hclosed hroot m hm i hmi hRi residue Q hQcard
  have hmass0 : 0 ≤ selectionMass P m := Finset.sum_nonneg (fun _ _ => by positivity)
  have hbudget := mul_le_mul_of_nonneg_right hsigmaBudget hmass0
  have hbound := weighted_two_exceptions (selections P m) (fun f => (selectionProduct f : ℝ)⁻¹) E EInv EHard
    (fun _ _ => by positivity) hsub
  change (∑ f ∈ (selections P m).filter E,(selectionProduct f : ℝ)⁻¹) ≤ tau*selectionMass P m
  have hfI := Finset.filter_congr_decidable (selections P m) EInv (fun f => Classical.propDecidable (EInv f))
  simp only [hfI] at hbound
  have hsummed := hbound.trans (add_le_add hInvBound hHardBound)
  apply hsummed.trans
  calc
    _ ≤ (tau/2)*selectionMass P m+(tau/2)*selectionMass P m := add_le_add hbudget le_rfl
    _ = _ := by ring

end ErdosVarianceFactory


end Erdos970

end OAI
