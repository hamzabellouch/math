import OAI.NumberTheory.DirichletL.Moments.SupportedTailAggregate
import OAI.NumberTheory.DirichletL.Moments.SourceSecondZeroEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondLocalization
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSourcePoisson CenteredMomentSecondWholeKernel CenteredMomentSecondTail
open CenteredMomentFirstLocalization CenteredMomentSectorLocalization CenteredMomentSupportedCorrelation
open CenteredMomentSupportedTailAggregate CenteredMomentSourceSecondZeroEnergy CenteredMomentSecondDiagonal
local notation "O" => ActualEisensteinCubic.O

def secondRetainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
    ∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
      actualCorrelation (primaryGenerator I) (primaryGenerator J)
        ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) (-h)*
      paperRadialFourier W (K*‖eisEmbedding h‖^2/
        ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2)

theorem secondSourceKernel_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    secondSourceKernel I J W K=
      (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
        actualCorrelation (primaryGenerator I) (primaryGenerator J)
          ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) 0*
          paperRadialFourier W 0+
      secondRetainedPair I J hI hJ W K Tsec Z ξ+
      secondDiscardedPair I J hI hJ W K Tsec Z ξ := by
  have hpI := (supported_span_primaryGenerator_iff I).mpr hI
  have hpJ := (supported_span_primaryGenerator_iff J).mpr hJ
  have hk : 0<K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) :=
    div_pos hK (mul_pos (CenteredMomentFirstScale.norm_pos I hI.1) (CenteredMomentFirstScale.norm_pos J hJ.1))
  have hs := lattice_fourier_split W _ hk
    (fun h => actualCorrelation (primaryGenerator I) (primaryGenerator J) hpI hpJ (-h))
    _ (fun h => CenteredMomentTail.actualCorrelation_norm_le _ _ hpI hpJ (-h))
    (frequencyRadius Tsec Z ξ)
  have he (h : O) : K*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2=
      (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*normValue h := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq I hI,primary_norm_sq J hJ,normValue_eq_embedding]
    ring
  rw [secondSourceKernel_poisson I J hI hJ W K hK]
  unfold secondRetainedPair secondDiscardedPair
  simp_rw [he]
  rw [hs]
  simp only [neg_zero]
  ring

def secondRetainedEnergy (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*heightCoeff η t I)*star (c J*heightCoeff η t J))*
      secondRetainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

theorem sourceGaussEnergy_localized (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    CenteredMomentOriginalChildEnergy.sourceGaussEnergy S β (heightCoeff η t) W K=
      ((K:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β η t+
      secondRetainedEnergy η t S β W K Tsec Z ξ+
      secondDiscardedEnergy η t S β W K Tsec Z ξ := by
  rw [sourceGaussEnergy_poisson η t S β W K hK]
  unfold sourceSecondZero secondZeroEnergy secondRetainedEnergy secondDiscardedEnergy
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  have he := secondSourceKernel_split I J (Finset.mem_filter.mp I.property).2
    (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ hK
  rw [secondSourceKernel_poisson I J (Finset.mem_filter.mp I.property).2
    (Finset.mem_filter.mp J.property).2 W K hK] at he
  simp only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2]
  convert congrArg (fun x : ℂ => ((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*x) he using 1 <;> ring

end SevenEighths.CenteredMomentSecondLocalization

end

end OAI
