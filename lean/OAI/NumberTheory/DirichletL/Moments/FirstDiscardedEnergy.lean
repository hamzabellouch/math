import OAI.NumberTheory.DirichletL.Moments.FirstDiscarded

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstDiscardedEnergy
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson ConcretePrimeRowBridge
open CenteredMomentFirstReduced CenteredMomentSectorLocalization CenteredMomentCorrelation
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstDiscarded CenteredMomentActive
open CenteredMomentCompleteCommon IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem tripleRow_norm_le_one (a b r : O) (ha : a≠0) (hb : b≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x,‖G x‖≤1) (z : O) :
    ‖tripleRow a b r χa χb G z‖≤1 := by
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  rw [tripleRow,norm_mul,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticInitialBound.norm_finite_character_le_one χa _)).trans
      (QuadraticInitialBound.norm_finite_character_le_one χb _))).trans (hG _)

theorem tripleFourier_norm_le_full (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x,‖G x‖≤1) (h : O) :
    ‖tripleFourier a b r ha hb hr χa χb G h‖≤normValue (a*(b*r)) := by
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  rw [tripleFourier,tsum_fintype]
  calc
    _ ≤ ∑ x : Residue (a*(b*r)),‖tripleResidue a b r χa χb G x*
      quotientTrace (a*(b*r)) (mul_ne_zero ha (mul_ne_zero hb hr)) (Ideal.Quotient.mk _ h*x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue (a*(b*r)),(1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [norm_mul,(quotientTrace _ _).norm_apply,mul_one,tripleResidue_mk]
      exact tripleRow_norm_le_one a b r ha hb χa χb G hG z
    _ = _ := by simp [normValue,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem activeFunction_norm_le_one (I J : Ideal O) (hI : CanonicalQuadraticSieve.Supported I)
    (x : Residue (activeConductor I J)) : ‖activeFunction I J hI x‖≤1 := by
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
  calc
    _ = ‖finiteSexticRow (activePrime I J) (activeGood I J hI)
        (CenteredMomentCanonicalFirst.activeExponent I J) z‖ :=
      congrArg norm (principalSexticRow_mk (activePrime I J) (activeCoprime I J)
        (activeGood I J hI) (CenteredMomentCanonicalFirst.activeExponent I J)
        (activeConductor I J) (span_finitePrimeModulus _) z)
    _ ≤ 1 := QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ z

theorem scaled_discarded_triple_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ k : ℝ),
      0<Tsec → 1<Z → 1≤Csec → 0<k →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ∀ (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
        (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
        (G : Residue r → ℂ), (∀ x,‖G x‖≤1) →
      kernelReference Tsec H≤k/normValue (a*(b*r)) →
      ‖((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
        (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
          tripleFourier a b r ha hb hr χa χb G h*
          paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h)‖ ≤
      k*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ k hT hZ hCs hk hthreshold a b r ha hb hr χa χb G hG hscale
  have hN : 0<normValue (a*(b*r)) := norm_pos _
    (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr)))
  have hh := ht W Tsec Z Csec H ξ (k/normValue (a*(b*r))) (normValue (a*(b*r)))
    hT hZ hCs hthreshold hscale hN.le (tripleFourier a b r ha hb hr χa χb G)
    (tripleFourier_norm_le_full a b r ha hb hr χa χb G hG)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hk hN)]
  apply (mul_le_mul_of_nonneg_left hh (div_pos hk hN).le).trans_eq
  field_simp

def canonicalDiscardedTerm (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
      (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

theorem canonical_kernel_scale (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (E : Finset (CommonIndex I J)) (K : ℝ) :
    (K/normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/
      normValue (residualGenerator I J*(residualGenerator J I*activeConductor I J)) =
      K/((Ideal.absNorm (∏ P∈E,P.val):ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (CenteredMomentCompleteCommon.residualPart I J):ℝ)*
        (Ideal.absNorm (CenteredMomentCompleteCommon.residualPart J I):ℝ)) := by
  rw [normValue_mul,normValue_mul]
  unfold normValue
  rw [primeSubsetGenerator,span_idealGenerator,residualGenerator_span I J hI,residualGenerator_span J I hJ,div_div]
  congr 1
  ring

theorem canonical_discarded_term_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O)
        (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
        (E : Finset (CommonIndex I J)) (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp HN*X → (Ideal.absNorm J:ℝ)≤Real.exp HN*X →
      firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖canonicalDiscardedTerm I J hI hJ E W K Tsec Z ξ‖ ≤
      K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := scaled_discarded_triple_bound A
  refine ⟨s,C,hC,?_⟩
  intro W I J hI hJ E K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  have he : e≠0 := primeSubsetGenerator_ne_zero _ _
  have hE : (∏ P∈E,P.val)≠(0:Ideal O) := by
    have hh := Ideal.span_singleton_eq_bot.not.mpr he
    simpa only [e,primeSubsetGenerator,span_idealGenerator,Ideal.zero_eq_bot] using hh
  have hNe : 0<normValue e := norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)
  have hNe1 : 1≤normValue e := by
    change (1:ℝ)≤(Ideal.absNorm (Ideal.span {e}):ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr he))
  have hk := div_pos hK hNe
  have hkK : K/normValue e≤K := div_le_self hK.le hNe1
  have hT := (firstNominalScale_pos I J _ hE K X hK hX).trans_le hsec
  have hscale := actual_first_kernel_reference I J _ hI.1 hJ.1 hE K X HN Tsec hK hX hi hj hsec
  rw [← canonical_kernel_scale I J hI hJ E K] at hscale
  have hb := ht W Tsec Z Csec HN ξ (K/normValue e) hT hZ hCs hk hthreshold
    (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
    (activeFunction_norm_le_one I J hI) hscale
  have hm : ‖(UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e‖≤1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticInitialBound.norm_ideal_moebius_le_one _)).trans
      (tripleRow_norm_le_one _ _ _ (supported_element_ne_zero _ (residualGenerator_supported I J hI))
        (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) _ _ _ (activeFunction_norm_le_one I J hI) e)
  change ‖_ * _‖≤_
  rw [norm_mul]
  apply (mul_le_mul hm hb (norm_nonneg _) zero_le_one).trans
  rw [one_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hkK (by positivity)) (by positivity)

def inactiveSubsets (I J : Ideal O) : Finset (Finset (CommonIndex I J)) :=
  (principalSupport (Finset.univ : Finset (CommonIndex I J)) (leftExponent I J) (rightExponent I J)).powerset

theorem inactiveSubsets_card (I J : Ideal O) :
    (inactiveSubsets I J).card≤2^(primeSupport I).card := by
  rw [inactiveSubsets,Finset.card_powerset]
  apply Nat.pow_le_pow_right (by norm_num)
  calc
    _ ≤ (Finset.univ : Finset (CommonIndex I J)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = (commonSupport I J).card := by simp [CommonIndex]
    _ ≤ _ := Finset.card_le_card Finset.inter_subset_left

def canonicalDiscardedPair (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K Tsec Z ξ

theorem canonical_discarded_pair_bound (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O)
        (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
        (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp HN*X → (Ideal.absNorm J:ℝ)≤Real.exp HN*X →
      (∀ E∈inactiveSubsets I J,firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec) →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖canonicalDiscardedPair I J hI hJ W K Tsec Z ξ‖ ≤
      (Ideal.absNorm I:ℝ)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_term_bound A
  obtain ⟨D,hD,hsub⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨s,D*C,mul_pos hD hC,?_⟩
  intro W I J hI hJ K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hc : ((inactiveSubsets I J).card:ℝ)≤D*(Ideal.absNorm I:ℝ)^ε := by
    apply le_trans _ (hsub I hI.1)
    exact_mod_cast inactiveSubsets_card I J
  calc
    _ ≤ ∑ E∈inactiveSubsets I J,‖canonicalDiscardedTerm I J hI hJ E W K Tsec Z ξ‖ := norm_sum_le _ _
    _ ≤ ∑ _E∈inactiveSubsets I J,
        K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) :=
      Finset.sum_le_sum (fun E hE => ht W I J hI hJ E K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj (hsec E hE) hthreshold)
    _ = ((inactiveSubsets I J).card:ℝ)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) := by simp
    _ ≤ (D*(Ideal.absNorm I:ℝ)^ε)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end SevenEighths.CenteredMomentFirstDiscardedEnergy

end

end OAI
