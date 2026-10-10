import OAI.NumberTheory.Jacobsthal.Estimates.ActualSourceInverse
import OAI.NumberTheory.Jacobsthal.Estimates.IsolatedPowerOrdering
import OAI.NumberTheory.Jacobsthal.Sieve.BoxWitnessFactorization

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.NormalizedBoxException
open ErdosCofactorChoices ErdosInverseCells ErdosInverseSampling CanonicalSubsetBox
open BoxWitnessFactorization ParentCofactorChoices BinCutSelections

attribute [local instance] Classical.propDecidable

theorem weighted_witness_le_total (P Q U : Finset ℕ) (W : (ℕ × ℕ) → ℕ → Prop) :
    weightedWitness P Q U W ≤ harmonicMass P*harmonicMass Q*harmonicMass U := by
  have hs : witnessPairs (P.product Q) U W ⊆ tripleSpace P Q U := Finset.filter_subset _ _
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hs (fun x _ _ => tripleWeight_nonneg x)
  exact hh.trans_eq (triple_weight_sum P Q U)

theorem unnormalize_witness (P Q U : Finset ℕ) (W : (ℕ × ℕ) → ℕ → Prop) (sigma : ℝ)
    (h : weightedWitness P Q U W/(harmonicMass P*harmonicMass Q*harmonicMass U) ≤ sigma) :
    weightedWitness P Q U W ≤ sigma*(harmonicMass P*harmonicMass Q*harmonicMass U) := by
  have hm : 0 ≤ harmonicMass P*harmonicMass Q*harmonicMass U :=
    mul_nonneg (mul_nonneg (harmonicMass_nonneg P) (harmonicMass_nonneg Q)) (harmonicMass_nonneg U)
  rcases hm.eq_or_lt with hm | hm
  · rw [← hm,mul_zero]
    have hh := weighted_witness_le_total P Q U W
    rwa [← hm] at hh
  · exact (div_le_iff₀ hm).mp h

theorem selection_exception_bound {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1) (W : (ℕ × ℕ) → ℕ → Prop) (sigma : ℝ)
    (h : weightedWitness (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j) W/
      (harmonicMass (P i)*harmonicMass (cofactorChoices P (parentCofactorMultiplicity m i j))*harmonicMass (P j)) ≤ sigma) :
    selectionWitnessMass P m i j W ≤ sigma*selectionMass P m := by
  have hw := unnormalize_witness (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j) W sigma h
  rw [selection_witness_factor P m hP hd i j hji hi hj,full_box_mass_factor P m hP hd i j hji hi hj]
  have hh := mul_le_mul_of_nonneg_left hw (harmonicMass_nonneg (cofactorChoices P (belowMultiplicity m j)))
  nlinarith
end NumberTheoryLean.NormalizedBoxException



namespace NumberTheoryLean.ActualInverseFullBoxMass
open ErdosInverseSampleCost ErdosCofactorChoices ErdosInverseCells ErdosInverseSampling ErdosInverseBoxApplication
open NormalizedBoxException BoxWitnessFactorization CanonicalSubsetBox ParentCofactorChoices


theorem actual_inverse_full_box_mass {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1)
    (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 S R Z cp sigma : ℝ) (F : ℕ)
    (hInv : SourceInverseConclusion Y small a delta V0 S R Z cp sigma F
      (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j)) :
    selectionWitnessMass P m i j (actualWitness Y small a delta V0 (P i) S R Z cp) ≤ sigma*selectionMass P m := by
  have hh := hInv.2.2.1
  rw [actual_exception_weight] at hh
  exact selection_exception_bound P m hP hd i j hji hi hj _ sigma hh
end NumberTheoryLean.ActualInverseFullBoxMass



namespace NumberTheoryLean.GeometricFullBoxInverse
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open GeometricBoxImages GeometricInverseGeometry BoundedEdgeBins ParentCofactorChoices
open JacobsthalSourceScale IsolatedSourceScales SourceNodeCoordinates
open ActualInverseFullBoxMass BoxWitnessFactorization CanonicalSubsetBox IsolatedPowerOrdering ErdosInverseSampleCost
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseBoxApplication
open LogarithmicBinScale LogarithmicBinEndpoints
open scoped Topology


theorem geometric_full_box_inverse (C Kstar aStar alpha delta sigma : ℝ)
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
      ∀ j : Fin (binCount (ErdosInverseBoxHeight.sourceW top) top xi),
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
            (lower w top xi i) (ErdosInverseBoxHeight.sourceZ top) cp) ≤ sigma*selectionMass (actualBins top xi) m := by
  obtain ⟨cp,hcp,F,xiI,hxiI,hxiI1,hInv⟩ := actual_source_inverse C (2*Kstar+4) aStar (2*Kstar+3) alpha delta sigma
    (by linarith) (by linarith) ha ha1 (by linarith) halpha hd hsigma hsigma1
  have hC0 : 0 < C := by linarith
  refine ⟨cp,hcp,F,min xiI (1/(2*C)),lt_min hxiI (by positivity),(min_le_left _ _).trans hxiI1,?_⟩
  intro xi hxi hxi₀
  have hxI := hxi₀.trans (min_le_left _ _)
  have hDelta : 2*C*xi ≤ 1 := by
    have hh := (le_div_iff₀ (show 0 < 2*C by positivity)).mp (hxi₀.trans (min_le_right _ _))
    nlinarith
  have hWT := sourceW_tendsto.comp Real.tendsto_log_atTop
  have hBT := sourceB_tendsto.comp Real.tendsto_log_atTop
  have hlargeT := (hBT.const_mul_atTop halpha).eventually_gt_atTop (2*Kstar+3)
  filter_upwards [hInv xi hxi hxI,ErdosCofactorChoices.source_span_geometry,
    Real.tendsto_log_atTop.eventually source_scale_eventually,
    Real.tendsto_log_atTop.eventually (source_isolated_search_scale halpha),
    hBT.eventually_ge_atTop 3,hWT.eventually_ge_atTop (Real.exp 1),hlargeT,
    eventually_gt_atTop (1:ℝ)] with top hInverse hspan hscale hsearch hB3 hWexp hlarge htop1
  change Real.exp 1 ≤ ErdosInverseBoxHeight.sourceW top at hWexp
  change 3 ≤ ErdosInverseBoxHeight.sourceB top at hB3
  change 2*Kstar+3 < alpha*ErdosInverseBoxHeight.sourceB top at hlarge
  have hw : 1 < ErdosInverseBoxHeight.sourceW top := hscale.1
  have htop : ErdosInverseBoxHeight.sourceW top < top := hspan.2.1
  have hlog : 1 ≤ Real.log (ErdosInverseBoxHeight.sourceW top) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hWexp
    simpa only [Real.log_exp] using hh
  have hpow : (ErdosInverseBoxHeight.sourceW top)^(ErdosInverseBoxHeight.sourceB top)=top :=
    (sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans htop1))
  refine ⟨hw,htop,?_⟩
  intro R L z hi h199 hz hcut hclosed hroot m hm
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hY : 0 < ErdosInverseBoxHeight.sourceY top := by
    by_contra! hn
    have hzero : ErdosInverseBoxHeight.sourceY top=0 := by omega
    rw [hzero,Nat.cast_zero,Real.log_zero,zero_div] at hroot
    have hg := node_gap_eq hs hz hcut
    nlinarith
  have hgeo := geometric_inverse_geometry (M:=2*Kstar+3) (X:=2*Kstar+3) hw htop hxi hC hlog hscale.2.2.2.2 hDelta hB3 hpow hsearch hlarge
    (ErdosInverseBoxHeight.sourceY top) hY z hroot hi h199 hz hcut hclosed m hm
  obtain ⟨i,hmi,hilo,hihi,hgeo⟩ := hgeo
  refine ⟨i,hmi,?_⟩
  intro j hj residue
  obtain ⟨hij,_hmj,hzi,hzj,hlen,_hUlo,hUhi,hparent,hchild⟩ := hgeo j hj
  have hji := source_power_before_edge hw htop hxi hpow m i j hilo hj hlarge
  have hmj := bounded_edge_singleton m j hj
  refine ⟨hji,hmj,?_⟩
  dsimp only
  have hresult := hInverse (parentCofactorMultiplicity m i j) i j hij hzi hzj hlen residue hilo hihi hUhi
    (by
      intro q hq p hp
      change Real.log ((ErdosInverseBoxHeight.sourceY top:ℝ)/((p:ℝ)*(q:ℝ)))/Real.log (ErdosInverseBoxHeight.sourceW top) ≤ _
      have hh := hparent q hq p hp
      nlinarith)
    (by
      intro q hq p hp u hu
      exact (by linarith : 3*aStar/4 ≤ aStar).trans (hchild q hq p hp u hu))
  refine ⟨hresult,?_⟩
  exact actual_inverse_full_box_mass (actualBins top xi) m
    (fun k _p hp => (bin_prime_in_source (zero_lt_one.trans hw) htop hxi k hp).1)
    (fun k l hkl => LogarithmicBinPartition.bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl)
    i j hji hmi hmj _ _ residue _ _ _ _ _ _ _ F hresult
end NumberTheoryLean.GeometricFullBoxInverse



namespace NumberTheoryLean.GeometricRangeInverse
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open GeometricBoxImages GeometricInverseGeometry BoundedEdgeBins ParentCofactorChoices
open JacobsthalSourceScale IsolatedSourceScales SourceNodeCoordinates
open ActualInverseFullBoxMass BoxWitnessFactorization CanonicalSubsetBox IsolatedPowerOrdering ErdosInverseSampleCost
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseBoxApplication
open LogarithmicBinScale LogarithmicBinEndpoints
open scoped Topology


theorem geometric_range_inverse (C Kstar aStar alpha delta sigma : ℝ)
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
      ∀ j : Fin (binCount (ErdosInverseBoxHeight.sourceW top) top xi),
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
            (lower w top xi i) (ErdosInverseBoxHeight.sourceZ top) cp) ≤ sigma*selectionMass (actualBins top xi) m := by
  obtain ⟨cp,hcp,F,xiI,hxiI,hxiI1,hInv⟩ := actual_source_inverse C (2*Kstar+4) aStar (2*Kstar+3) alpha delta sigma
    (by linarith) (by linarith) ha ha1 (by linarith) halpha hd hsigma hsigma1
  have hC0 : 0 < C := by linarith
  refine ⟨cp,hcp,F,min xiI (1/(2*C)),lt_min hxiI (by positivity),(min_le_left _ _).trans hxiI1,?_⟩
  intro xi hxi hxi₀
  have hxI := hxi₀.trans (min_le_left _ _)
  have hDelta : 2*C*xi ≤ 1 := by
    have hh := (le_div_iff₀ (show 0 < 2*C by positivity)).mp (hxi₀.trans (min_le_right _ _))
    nlinarith
  have hWT := sourceW_tendsto.comp Real.tendsto_log_atTop
  have hBT := sourceB_tendsto.comp Real.tendsto_log_atTop
  have hlargeT := (hBT.const_mul_atTop halpha).eventually_gt_atTop (2*Kstar+3)
  filter_upwards [hInv xi hxi hxI,ErdosCofactorChoices.source_span_geometry,
    Real.tendsto_log_atTop.eventually source_scale_eventually,
    Real.tendsto_log_atTop.eventually (source_isolated_search_scale halpha),
    hBT.eventually_ge_atTop 3,hWT.eventually_ge_atTop (Real.exp 1),hlargeT,
    eventually_gt_atTop (1:ℝ)] with top hInverse hspan hscale hsearch hB3 hWexp hlarge htop1
  change Real.exp 1 ≤ ErdosInverseBoxHeight.sourceW top at hWexp
  change 3 ≤ ErdosInverseBoxHeight.sourceB top at hB3
  change 2*Kstar+3 < alpha*ErdosInverseBoxHeight.sourceB top at hlarge
  have hw : 1 < ErdosInverseBoxHeight.sourceW top := hscale.1
  have htop : ErdosInverseBoxHeight.sourceW top < top := hspan.2.1
  have hlog : 1 ≤ Real.log (ErdosInverseBoxHeight.sourceW top) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hWexp
    simpa only [Real.log_exp] using hh
  have hpow : (ErdosInverseBoxHeight.sourceW top)^(ErdosInverseBoxHeight.sourceB top)=top :=
    (sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans htop1))
  refine ⟨hw,htop,?_⟩
  intro R L z hi h199 hz hcut hclosed hroot m hm
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hY : 0 < ErdosInverseBoxHeight.sourceY top := by
    by_contra! hn
    have hzero : ErdosInverseBoxHeight.sourceY top=0 := by omega
    rw [hzero,Nat.cast_zero,Real.log_zero,zero_div] at hroot
    have hg := node_gap_eq hs hz hcut
    nlinarith
  have hgeo := geometric_inverse_geometry (M:=2*Kstar+3) (X:=2*Kstar+3) hw htop hxi hC hlog hscale.2.2.2.2 hDelta hB3 hpow hsearch hlarge
    (ErdosInverseBoxHeight.sourceY top) hY z hroot hi h199 hz hcut hclosed m hm
  obtain ⟨i,hmi,hilo,hihi,hgeo⟩ := hgeo
  refine ⟨i,hmi,hilo,hihi,?_⟩
  intro j hj residue
  obtain ⟨hij,_hmj,hzi,hzj,hlen,_hUlo,hUhi,hparent,hchild⟩ := hgeo j hj
  have hji := source_power_before_edge hw htop hxi hpow m i j hilo hj hlarge
  have hmj := bounded_edge_singleton m j hj
  refine ⟨hji,hmj,?_⟩
  dsimp only
  have hresult := hInverse (parentCofactorMultiplicity m i j) i j hij hzi hzj hlen residue hilo hihi hUhi
    (by
      intro q hq p hp
      change Real.log ((ErdosInverseBoxHeight.sourceY top:ℝ)/((p:ℝ)*(q:ℝ)))/Real.log (ErdosInverseBoxHeight.sourceW top) ≤ _
      have hh := hparent q hq p hp
      nlinarith)
    (by
      intro q hq p hp u hu
      exact (by linarith : 3*aStar/4 ≤ aStar).trans (hchild q hq p hp u hu))
  refine ⟨hresult,?_⟩
  exact actual_inverse_full_box_mass (actualBins top xi) m
    (fun k _p hp => (bin_prime_in_source (zero_lt_one.trans hw) htop hxi k hp).1)
    (fun k l hkl => LogarithmicBinPartition.bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl)
    i j hji hmi hmj _ _ residue _ _ _ _ _ _ _ F hresult
end NumberTheoryLean.GeometricRangeInverse


end Erdos970

end OAI
