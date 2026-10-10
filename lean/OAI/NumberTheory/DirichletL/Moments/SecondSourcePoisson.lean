import OAI.NumberTheory.DirichletL.Moments.SecondSourceEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourcePoisson
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentFourier CenteredMomentPoisson
open CenteredMomentSecondSourceEnergy CenteredMomentSupportedCorrelation CenteredMomentRowNorm
local notation "O" => ActualEisensteinCubic.O

theorem secondSourceKernel_poisson (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    secondSourceKernel I J W K=
      (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
        ∑' h : O,actualCorrelation (primaryGenerator I) (primaryGenerator J)
          (by rw [primary_span_supported I hI];exact hI)
          (by rw [primary_span_supported J hJ];exact hJ) (-h)*
          paperRadialFourier W (K*‖eisEmbedding h‖^2/
            ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2) := by
  unfold secondSourceKernel
  simp only [primaryGaussRow,dite_eq_left hI,dite_eq_left hJ,gaussRow]
  rw [sextic_gauss_pair_poisson _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ) W K hK]
  simp only [primary_span_supported I hI,primary_span_supported J hJ]

theorem sourceGaussEnergy_poisson (τ : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    sourceGaussEnergy S β (heightCoeff τ t) W K=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*
          ((K:ℂ)/((Real.sqrt (Ideal.absNorm (I:Ideal O):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (J:Ideal O):ℝ):ℂ)))*
            ∑' h : O,actualCorrelation (sourceGenerator S I) (sourceGenerator S J)
              (sourceGenerator_supported S I) (sourceGenerator_supported S J) (-h)*
              paperRadialFourier W (K*‖eisEmbedding h‖^2/
                ‖eisEmbedding (sourceGenerator S I*sourceGenerator S J)‖^2) := by
  rw [sourceGaussEnergy,gaussEnergy_poisson _ _ _ _ W K hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2]
  ring

end SevenEighths.CenteredMomentSecondSourcePoisson

end

end OAI
