import OAI.NumberTheory.DirichletL.Moments.SecondSectorFrequency
import OAI.NumberTheory.DirichletL.Moments.SecondLocalization

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSectorRetained
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorFrequency CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLedger CenteredMomentCanonicalFirst
open CenteredMomentSecondWholeKernel CenteredMomentFirstLocalization CenteredMomentSectorLocalization
open CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

def physicalKernel (C D : Ideal O) (W : 𝓢(ℝ,ℂ)) (K R : ℝ)
    (j : O) (I J : Ideal O) : ℂ :=
  ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*I):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*J):ℝ):ℂ)))*
    (retainedWeight R (normValue j):ℂ)*
      paperRadialFourier W (K*‖eisEmbedding j‖^2/
        ‖eisEmbedding (primaryGenerator (C*I)*primaryGenerator (D*J))‖^2)

theorem physical_sector_summable (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    Summable (sectorFrequency η t S β C D hC hD (physicalKernel C D W K R)) := by
  unfold sectorFrequency
  apply summable_sum
  intro I hI
  apply summable_sum
  intro J hJ
  by_cases hcop : IsCoprime (I:Ideal O) (J:Ideal O)
  · simp only [ite_eq_left hcop]
    have hCI : Supported (C*(I:Ideal O)) := (supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩
    have hDJ : Supported (D*(J:Ideal O)) := (supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩
    have hk : 0<K/((Ideal.absNorm (C*(I:Ideal O)):ℝ)*Ideal.absNorm (D*(J:Ideal O))) :=
      div_pos hK (mul_pos (CenteredMomentFirstScale.norm_pos _ hCI.1) (CenteredMomentFirstScale.norm_pos _ hDJ.1))
    have hc (j : O) : ‖idealCorrelation (C*I) (D*J) hCI hDJ j‖≤
        (Ideal.absNorm (C*(I:Ideal O)):ℝ)*Ideal.absNorm (D*(J:Ideal O)) := by
      have hh := CenteredMomentTail.actualCorrelation_norm_le _ _
        ((supported_span_primaryGenerator_iff _).mpr hCI) ((supported_span_primaryGenerator_iff _).mpr hDJ) j
      simpa only [CenteredMomentSupport.idealCorrelation,primary_span_supported _ hCI,primary_span_supported _ hDJ] using hh
    have hs := weighted_fourier_summable W _ hk
      (fun j=>idealCorrelation (C*I) (D*J) hCI hDJ j)
      (fun j=>(retainedWeight R (normValue j):ℂ)) _ hc (fun j=>retained_complex_norm R _)
    have he (j : O) : K*‖eisEmbedding j‖^2/‖eisEmbedding (primaryGenerator (C*I)*primaryGenerator (D*J))‖^2=
        (K/((Ideal.absNorm (C*(I:Ideal O)):ℝ)*Ideal.absNorm (D*(J:Ideal O))))*normValue j := by
      rw [map_mul,norm_mul,mul_pow,primary_norm_sq _ hCI,primary_norm_sq _ hDJ,normValue_eq_embedding]
      ring
    convert hs.mul_left
      (((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
        ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*(I:Ideal O)):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*(J:Ideal O)):ℝ):ℂ)))) using 1
    funext j
    dsimp only [physicalKernel]
    rw [he]
    ring
  · simp only [ite_eq_right hcop,zero_mul]
    exact summable_zero

theorem actual_retained_sector_GV (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    (∑' j : O,sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) j)=
      ∑ U : Finset (CommonIndex C D),∑' h : O,
        if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
          sectorFrequency η t S β C D hC hD (physicalKernel C D W K R)
            ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) else 0 := by
  rw [sectorFrequency_tsum_common η t S β C D hC hD hCD]
  rw [sectorFrequency_tsum_partition η t S β C D hC hD _
    ((physical_sector_summable η t S β C D hC hD W K R hK).comp_injective
      (mul_right_injective₀ (commonFrequencyGenerator_ne_zero C D hC)))]
  exact Finset.sum_congr rfl (fun U _=>sectorFrequency_partition_nonunit η t S β C D hC hD U _)

end SevenEighths.CenteredMomentSecondSectorRetained

end

end OAI
