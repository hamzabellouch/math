import OAI.NumberTheory.DirichletL.Moments.SecondRadicalBudget
import OAI.NumberTheory.DirichletL.Moments.SectorLocalization

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondActualWidth
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondRadicalBudget CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentSupport CenteredMomentDescentLedger
open CenteredMomentPartitionNorm CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem actual_common_log_ge_unit (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)≤Real.logb Z (normValue (commonFrequencyGenerator C D)) := by
  have hh:=common_log_ge_unit (commonPrime C D) (commonPrime_supported C D hC)
    (leftExponent C D) (rightExponent C D) (leftExponent_pos C D) (rightExponent_pos C D) U Z hZ
  rw [←commonFrequencyGenerator_span C D hC] at hh
  simpa only [unitIdeal,commonPrime_span C D hC,normValue] using hh

theorem actual_width_bound (η τ : Character) (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z Tsec Csec L ξ : ℝ)
    (hZ : 1<Z) (hCsec : 0<Csec) (hT : Tsec≤Csec*Z^L)
    (hτ : Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z (fixedFactor:ℝ)+Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ))
    (h : O) (hne : retainedWeight (frequencyRadius Tsec Z ξ)
      (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))≠0) :
    max 0 (L-Real.logb Z (normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))+
      frequencyLoss Z Csec ξ)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
      L+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z (fixedFactor:ℝ)+frequencyLoss Z Csec ξ-
        (Real.logb Z (normValue (commonFrequencyGenerator C D))-
          Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)) := by
  have hn:=actual_nonempty_width_of_weight Tsec Z Csec L ξ hZ hCsec hT _ h hne
  rw [max_eq_right hn]
  have hg := normValue_pos (commonFrequencyGenerator C D)
    (CenteredMomentSecondCanonicalFrequency.commonFrequencyGenerator_ne_zero C D hC)
  have hv := normValue_pos (nonunitFrequencyGenerator C D U)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  rw [normValue_mul,Real.logb_mul hg.ne' hv.ne']
  change _≤_
  change Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
    Real.logb Z (fixedFactor:ℝ)+Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
      Real.logb Z (normValue (nonunitFrequencyGenerator C D U)) at hτ
  linarith

theorem exists_actual_width_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ:Character,
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        CanonicalRowCompletion.idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD:Supported D),primeSupport C=primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      ∀Z Tsec Csec L ξ M σ:ℝ,1<Z → 0<Csec → Tsec≤Csec*Z^L →
      L+Real.logb Z (η.modulus.absNorm:ℝ)≤M-σ →
      ∀h:O,retainedWeight (frequencyRadius Tsec Z ξ)
        (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))≠0 →
      max 0 (L-Real.logb Z (normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))+
        frequencyLoss Z Csec ξ)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          M-σ+Real.logb Z (fixedFactor:ℝ)+frequencyLoss Z Csec ξ := by
  obtain ⟨τ,he,ht,hN⟩:=exists_second_log_budgeted_family η χ C D hC U
  refine ⟨τ,ht,?_⟩
  intro hD hCD w hw Z Tsec Csec L ξ M σ hZ hCs hT hnom h hh
  have hb:=actual_width_bound η τ C D hC U Z Tsec Csec L ξ hZ hCs hT
    (hN hD hCD w hw Z hZ) h hh
  have hg:=actual_common_log_ge_unit C D hC U Z hZ
  linarith

end SevenEighths.CenteredMomentSecondActualWidth

end

end OAI
