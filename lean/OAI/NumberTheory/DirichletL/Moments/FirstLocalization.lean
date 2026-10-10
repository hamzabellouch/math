import OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate
import OAI.NumberTheory.DirichletL.Moments.FirstEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstLocalization
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentFirstTailAggregate
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentFirstEnergy
local notation "O" => ActualEisensteinCubic.O

theorem weighted_fourier_summable (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0<k)
    (c w : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤B) (hw : ∀ h,‖w h‖≤1) :
    Summable (fun h : O => w h*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := paperRadialFourier_lattice_summable_norm W k hk
  simp_rw [← normValue_eq_embedding] at hs
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs.mul_left B)
  intro h
  rw [norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_left (norm_nonneg _) (hw h)).trans (hc h)) (norm_nonneg _)

theorem retained_complex_norm (R q : ℝ) : ‖(retainedWeight R q:ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (retainedWeight_nonneg R q)]
  exact (retainedWeight_bounds R q).2

theorem discarded_complex_norm (R q : ℝ) : ‖(discardedWeight R q:ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (discardedWeight_nonneg R q)]
  exact (discardedWeight_bounds R q).2

theorem lattice_fourier_split (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0<k)
    (c : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤B) (R : ℝ) :
    (∑' h : O,c h*paperRadialFourier W (k*normValue h))=
      c 0*paperRadialFourier W 0+
        (∑' h : O,(retainedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h))+
        (∑' h : O,(discardedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := weighted_fourier_summable W k hk c (fun _ => 1) B hc (by simp)
  simp only [one_mul] at hs
  have hr := weighted_fourier_summable W k hk c (fun h => (retainedWeight R (normValue h):ℂ)) B hc
    (fun h => retained_complex_norm R _)
  have hd := weighted_fourier_summable W k hk c (fun h => (discardedWeight R (normValue h):ℂ)) B hc
    (fun h => discarded_complex_norm R _)
  rw [hs.tsum_eq_add_tsum_ite 0]
  have hzero : normValue (0:O)=0 := by simp [normValue]
  simp only [hzero,mul_zero]
  rw [add_assoc,← hr.tsum_add hd]
  congr 1
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · subst h
    simp only [ite_true,hzero,
      retainedWeight_zero_nonpos R 0 le_rfl,discardedWeight_zero_nonpos R 0 le_rfl,
      Complex.ofReal_zero,zero_mul,add_zero]
  · rw [ite_eq_right hh]
    have hp : 0<normValue h := norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr hh)
    have he : (retainedWeight R (normValue h):ℂ)+(discardedWeight R (normValue h):ℂ)=1 := by
      exact_mod_cast retained_add_discarded R (normValue h) hp
    rw [← add_mul,← add_mul,he,one_mul]

def canonicalRetainedTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
      (retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

def canonicalZeroTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*
      (tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
        (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) 0*paperRadialFourier W 0))

def canonicalRetainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalRetainedTerm I J hI hJ E W K Tsec Z ξ

def canonicalZeroPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalZeroTerm I J hI hJ E W K

theorem reducedFirstSum_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    reducedFirstSum I J hI hJ W K=canonicalZeroPair I J hI hJ W K+
      canonicalRetainedPair I J hI hJ W K Tsec Z ξ+canonicalDiscardedPair I J hI hJ W K Tsec Z ξ := by
  unfold reducedFirstSum canonicalZeroPair canonicalRetainedPair canonicalDiscardedPair
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only [canonicalZeroTerm,canonicalRetainedTerm,canonicalDiscardedTerm]
  simp_rw [← normValue_eq_embedding]
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  have ha : a≠0 := supported_element_ne_zero _ (residualGenerator_supported I J hI)
  have hb : b≠0 := supported_element_ne_zero _ (residualGenerator_supported J I hJ)
  have hr : r≠0 := finitePrimeModulus_ne_zero _
  have he : primeSubsetGenerator (fun P : CommonIndex I J => P.val) E≠0 := primeSubsetGenerator_ne_zero _ _
  have hk : 0<(K/normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/normValue (a*(b*r)) :=
    div_pos (div_pos hK (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)))
      (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr))))
  have hh := lattice_fourier_split W _ hk
    (tripleFourier a b r ha hb hr (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (normValue (a*(b*r)))
    (tripleFourier_norm_le_full a b r ha hb hr _ _ _ (activeFunction_norm_le_one I J hI))
    (frequencyRadius Tsec Z ξ)
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let k := (K/normValue e)/normValue (a*(b*r))
  let F := tripleFourier a b r ha hb hr (residualCharacter I J hI)
    (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
  let d := (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e
  change d*((k:ℂ)*∑' h : O,F h*paperRadialFourier W ((K/normValue e)*normValue h/normValue (a*(b*r))))=
    d*((k:ℂ)*(F 0*paperRadialFourier W 0))+
      d*((k:ℂ)*∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))+
      d*((k:ℂ)*∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))
  have heq (h : O) : (K/normValue e)*normValue h/normValue (a*(b*r))=k*normValue h := by dsimp [k];ring
  simp_rw [heq]
  rw [hh]
  ring

def retainedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalRetainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

def zeroEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalZeroPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K

theorem finiteHeckeEnergy_localized (η : Character) (m A : O) (t : ℝ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K=
      zeroEnergy η m A t S c W K+retainedEnergy η m A t S c W K Tsec Z ξ+
        discardedEnergy η m A t S c W K Tsec Z ξ := by
  rw [finiteHeckeEnergy_reduced_poisson η m A t hmLam hm2 S c W K hK]
  simp_rw [reducedFirstSum_split _ _ _ _ W K Tsec Z ξ hK,mul_add,Finset.sum_add_distrib]
  rfl

end SevenEighths.CenteredMomentFirstLocalization

end

end OAI
