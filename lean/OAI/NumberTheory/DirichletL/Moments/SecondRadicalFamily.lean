import OAI.NumberTheory.DirichletL.Moments.SecondSixthSource
import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
import OAI.NumberTheory.DirichletL.Moments.RadicalFamily

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst (CommonIndex)
open CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource
open CenteredMomentRadicalFamily CenteredMomentSecondHeightFamily CenteredMomentSecondChildProfile
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentCommonSupport RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem active_radical_product (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) :
    (∏ P : ActiveIndex C D U,Ideal.span {activePrime C D U P})=
      ∏ P∈fixedActiveSet C D U,P.val := by
  simp only [activePrime,commonPrime_span C D hC]
  exact Finset.prod_coe_sort _ (fun P : CommonIndex C D=>P.val)

theorem exists_second_radical_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      τ.modulus.absNorm≤(childCharacter η χ).modulus.absNorm*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (∏P∈fixedActiveSet C D U,P.val).absNorm ∧
      (∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
        fixedBadMask 1 (reducedNumerator C D U) n) ∧
      ∀I:Ideal O,Supported I → ∀t:ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hM,hN,hτ⟩ := exists_radical_row_presentation (childCharacter η χ) fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    (activePrime C D U) (fun P=>commonPrime_supported C D hC P.val)
    (activeExponent C D U) (activeExponent_pos C D U)
  have he (n:O) : elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n := by
    rw [reducedNumerator_active_product]
    exact hτ n
  refine ⟨τ,?_,he,?_⟩
  · rw [←map_prod,active_radical_product C D hC U] at hN
    exact hN
  · intro I hI t
    have ht := idealCoeff_eq_row (childCharacter η χ) τ fixedBadMask 1
      (reducedNumerator C D U) he I
    change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
    rw [ht,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
    simp only [one_pow,mul_one]
    rw [heightCoeff_eq_fixed_rowWeight η t I hI]
    simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk]
    ring_nf

end SevenEighths.CenteredMomentSecondRadicalFamily

end

end OAI
