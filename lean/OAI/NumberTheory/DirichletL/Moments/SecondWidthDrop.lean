import OAI.NumberTheory.DirichletL.Moments.SecondActualWidth

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondWidthDrop
open HeckeFamily CenteredMomentSecondActualWidth CenteredMomentSecondRadicalBudget
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
local notation "O" => HeckeFamily.O

def amplificationIncrement (η:Character) (Z H K M σ:ℝ) : ℝ :=
  max (2*Real.logb Z H-Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-M) 0+σ

def nominalLength (Z H K g:ℝ) : ℝ := 2*Real.logb Z H-Real.logb Z K-g

lemma physical_frequency_scale (Z H K g:ℝ) (hZ:1<Z) (hH:0<H) (hK:0<K) :
    H^2/(K*Z^g)=Z^(nominalLength Z H K g) := by
  have hzg:0<Z^g:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hp:0<H^2/(K*Z^g):=div_pos (sq_pos_of_pos hH) (mul_pos hK hzg)
  have he:Real.logb Z (H^2/(K*Z^g))=nominalLength Z H K g := by
    rw [Real.logb_div (sq_pos_of_pos hH).ne' (mul_pos hK hzg).ne',Real.logb_pow,
      Real.logb_mul hK.ne' hzg.ne',Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)]
    unfold nominalLength
    norm_num
    ring
  rw [←he,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) hp]

lemma actual_nominal_drop (η:Character) (Z H K M σ:ℝ) :
    nominalLength Z H K (amplificationIncrement η Z H K M σ)+
      Real.logb Z (η.modulus.absNorm:ℝ)≤M-σ := by
  have hh:=le_max_left (2*Real.logb Z H-Real.logb Z K+
    Real.logb Z (η.modulus.absNorm:ℝ)-M) 0
  unfold nominalLength amplificationIncrement
  linarith

theorem exists_physical_width_family (η:Character) (χ:RayCharacter)
    (C D:Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D)) :
    ∃τ:Character,
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        CanonicalRowCompletion.idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD:Supported D),CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      ∀Z H K Tsec Csec ξ M σ g:ℝ,1<Z → 0<H → 0<K → 0<Csec →
      amplificationIncrement η Z H K M σ≤g →
      Tsec≤Csec*(H^2/(K*Z^g)) →
      ∀h:O,retainedWeight (frequencyRadius Tsec Z ξ)
        (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))≠0 →
      max 0 (nominalLength Z H K g-
        Real.logb Z (normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))+
        frequencyLoss Z Csec ξ)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          M-σ+Real.logb Z (fixedFactor:ℝ)+frequencyLoss Z Csec ξ := by
  obtain ⟨τ,hτ,hw⟩:=exists_actual_width_family η χ C D hC U
  refine ⟨τ,hτ,?_⟩
  intro hD hCD w hn Z H K Tsec Csec ξ M σ g hZ hH hK hCs hg hscale h hret
  apply hw hD hCD w hn Z Tsec Csec (nominalLength Z H K g) ξ M σ hZ hCs
  · rwa [←physical_frequency_scale Z H K g hZ hH hK]
  · have hh:=actual_nominal_drop η Z H K M σ
    unfold nominalLength at hh ⊢
    linarith
  · exact hret

end SevenEighths.CenteredMomentSecondWidthDrop

end

end OAI
