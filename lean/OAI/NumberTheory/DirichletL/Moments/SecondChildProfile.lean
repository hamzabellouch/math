import OAI.NumberTheory.DirichletL.Moments.FirstChildProfile
import OAI.NumberTheory.DirichletL.Moments.SecondScaled

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondChildProfile
open HeckeFamily HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow CenteredMomentChildAssembly
open CenteredMomentSecondScaled CanonicalRowCompletion CanonicalQuadraticSieve RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O

theorem child_ideal_primary (η : Character) (χ : RayCharacter)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (childCharacter η χ) I=idealCoeff η I*rayCharacter χ (CompletedGauss.primaryGenerator I) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have hc := idealCoeff_span (childCharacter η χ) hn
  have he := idealCoeff_span η hn
  rw [hs] at hc he
  rw [hc,childCharacter_primary η χ _ (by rw [hs];exact hI)
    (CompletedGauss.primaryGenerator_spec I hn).2,←he]

theorem exists_second_height_character (η : Character) (χ : RayCharacter) (m A : O)
    (hm : m≠0) (hA : A≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : Character,τ.modulus.absNorm≤rowConductorBound (childCharacter η χ) m 1 A ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom A I*
          rayCharacter χ (CompletedGauss.primaryGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_row_character_with_conductor (childCharacter η χ) m 1 A hm one_ne_zero hA hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have he := idealCoeff_eq_row (childCharacter η χ) τ m 1 A hτ I
  simp only [one_pow,mul_one] at he
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*
      idealRowHom A I*rayCharacter χ (CompletedGauss.primaryGenerator I)
  rw [he,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
  simp only [mul_one]
  ring

theorem second_divisor_column (η τ : Character) (χ : RayCharacter) (m A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom A I*
        rayCharacter χ (CompletedGauss.primaryGenerator I))
    (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => CompletedGauss.primaryGenerator J)
      (movingCoefficient A (fun J : Ideal O => CompletedGauss.primaryGenerator J)
        (fun J => β J*rowWeight η m 1 1 t J)) χ I=
      (if L∣I then β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,primary_span_supported I hI,hτ I hI t]
  split_ifs <;> ring

end SevenEighths.CenteredMomentSecondChildProfile

end

end OAI
