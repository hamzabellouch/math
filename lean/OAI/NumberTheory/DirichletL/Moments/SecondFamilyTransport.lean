import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
import OAI.NumberTheory.DirichletL.Moments.RestrictedEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondFamilyTransport
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondHeightFamily CenteredMomentSecondChildProfile CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredExceptionalProfile CenteredMomentRestrictedEnergy RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem row_presentation_height (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (I : Ideal O) (hI : Supported I) (t : ℝ) :
    heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I) := by
  have he := idealCoeff_eq_row (childCharacter η χ) τ fixedBadMask 1 A hτ I
  have he' : heightCoeff τ t I=rowWeight (childCharacter η χ) fixedBadMask 1 A t I := by
    change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
    rw [he]
    simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,one_pow,one_mul,mul_one]
  rw [he',rowWeight_split,←heightCoeff_eq_fixed_rowWeight (childCharacter η χ) t I hI]
  simp only [heightCoeff,child_ideal_primary η χ I hI]
  ring

theorem exists_second_family_presentation (η : Character) (χ : RayCharacter)
    (A : O) (hA : A≠0) :
    ∃ τ : Character,
      τ.modulus.absNorm≤rowConductorBound (childCharacter η χ) fixedBadMask 1 A ∧
      (∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n) ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_row_character_with_conductor (childCharacter η χ) fixedBadMask 1 A
    fixedBadMask_ne_zero one_ne_zero hA (dvd_mul_right _ _) (dvd_mul_left _ _)
  exact ⟨τ,hN,hτ,fun I hI t => row_presentation_height η τ χ A hτ I hI t⟩

theorem row_presentation_twist (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (z n : O) :
    rowTwist (elementHom τ) fixedBadMask 1 z n=
      rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 (A*z) n := by
  by_cases hn : Supported (Ideal.span {n})
  · have hc : coprimalityMask fixedBadMask n=1 := by
      change (if IsCoprime fixedBadMask n then (1:ℂ) else 0)=1
      rw [ite_eq_left (fixedBadMask_coprime n hn)]
    have ht := hτ n
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn] at ht
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn,rowTwist_extract_sixth_mask _ _ _ _ n hn]
    change elementCoeff τ n*coprimalityMask fixedBadMask n*idealRowHom (1^4*z) (Ideal.span {n})=_
    rw [ht,hc]
    simp only [one_pow,one_mul,mul_one,idealRowHom_argument_mul]
    ring
  · have hmLam : ConcretePrimeRowBridge.goodLambda∣fixedBadMask := dvd_mul_right _ _
    have hm2 : (2:O)∣fixedBadMask := dvd_mul_left _ _
    exact (rowTwist_zero_of_not_supported (elementHom τ) fixedBadMask 1 z n hmLam hm2 hn).trans
      (rowTwist_zero_of_not_supported (elementHom (childCharacter η χ)) fixedBadMask 1 (A*z) n hmLam hm2 hn).symm

theorem fixedInducingRow_transport (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (Q : Ideal O) (z : O) :
    FixedInducingRow τ Q fixedBadMask 1 z ↔
      FixedInducingRow (childCharacter η χ) Q fixedBadMask A z := by
  unfold FixedInducingRow
  simp only [one_mul,row_presentation_twist η τ χ A hτ]

theorem nonexceptional_transport (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (Q : Ideal O) (z : O) :
    nonexceptional η χ Q fixedBadMask A z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [nonexceptional,fixedInducingRow_transport η τ χ A hτ Q z]

end SevenEighths.CenteredMomentSecondFamilyTransport

end

end OAI
