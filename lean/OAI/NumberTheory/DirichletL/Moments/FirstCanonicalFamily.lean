import OAI.NumberTheory.DirichletL.Moments.FirstFamily
import OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
import OAI.NumberTheory.DirichletL.Moments.Primitive

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstCanonicalFamily
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstFamily
open CenteredMomentFirstColumns CenteredMomentPrimitive CenteredMomentCommonSupport RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem supported_of_dvd (A B : Ideal O) (hB : Supported B) (hd : A∣B) : Supported A := by
  obtain ⟨Q,hQ⟩ := hd
  rw [hQ] at hB
  exact ((supported_mul_iff A Q).mp hB).1

theorem activeConductor_supported (I J : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {activeConductor I J}) :=
  supported_of_dvd _ _ (commonPart_supported I J hI) (activeConductor_span_dvd I J)

theorem subsetGenerator_span_dvd (I J : Ideal O) (E : Finset (CommonIndex I J)) :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E}∣commonPart I J := by
  rw [primeSubsetGenerator,span_idealGenerator]
  refine (Finset.prod_dvd_prod_of_subset E Finset.univ
    (fun P : CommonIndex I J => P.val) (Finset.subset_univ _)).trans ?_
  rw [commonPart_left_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (leftExponent_pos I J P)

theorem subsetGenerator_supported (I J : Ideal O) (hI : Supported I)
    (E : Finset (CommonIndex I J)) :
    Supported (Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E}) :=
  supported_of_dvd _ _ (commonPart_supported I J hI) (subsetGenerator_span_dvd I J E)

def canonicalActiveCharacter (I J : Ideal O) (hI : Supported I) :
    MulChar (Residue (activeConductor I J)) ℂ :=
  primitiveCharacter (activePrime I J) (activeCoprime I J) (activeGood I J hI) (activeExponent I J)

@[simp] theorem canonicalActiveCharacter_mk (I J : Ideal O) (hI : Supported I) (n : O) :
    canonicalActiveCharacter I J hI (Ideal.Quotient.mk _ n)=
      finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J) n :=
  primitiveCharacter_mk _ _ _ _ n

theorem exists_canonical_first_pair (η : Character) (m : O) (hm : m≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (I J : Ideal O) (hI : Supported I) (E : Finset (CommonIndex I J))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
    let r := activeConductor I J
    let ρ := finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
        elementCoeff τ₁ n=elementCoeff η n*coprimalityMask m n*leftCoefficient e r ρ n*rayCharacter ξ₁ n) ∧
      (∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
        elementCoeff τ₂ n=elementCoeff η n*coprimalityMask m n*rightCoefficient e r ρ n*rayCharacter ξ₂ n) := by
  dsimp only
  obtain ⟨τ₁,hM₁,_,h₁⟩ := exists_first_character η m
    (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) (activeConductor I J) hm
    (subsetGenerator_supported I J hI E) (activeConductor_supported I J hI) hmLam hm2
    (canonicalActiveCharacter I J hI) ξ₁
  obtain ⟨τ₂,hM₂,_,h₂⟩ := exists_first_character η m
    (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) (activeConductor I J) hm
    (subsetGenerator_supported I J hI E) (activeConductor_supported I J hI) hmLam hm2
    (canonicalActiveCharacter I J hI)⁻¹ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro n hn hp
    rw [h₁ n hn hp,canonicalActiveCharacter_mk,leftCoefficient]
    ring
  · intro n hn hp
    let : Finite (Residue (activeConductor I J)) := finite_quotient_span (finitePrimeModulus_ne_zero (activePrime I J))
    rw [h₂ n hn hp,← MulChar.star_apply',canonicalActiveCharacter_mk,rightCoefficient]
    ring

theorem first_displayed_norm (η : Character) (m : O) (I J : Ideal O)
    (E : Finset (CommonIndex I J)) :
    (η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E*activeConductor I J}).absNorm =
    η.modulus.absNorm*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*
      ((∏ P∈E,P.val).absNorm*(Ideal.span {activeConductor I J}).absNorm) := by
  rw [← Ideal.span_singleton_mul_span_singleton,primeSubsetGenerator,span_idealGenerator]
  simp only [map_mul]

end SevenEighths.CenteredMomentFirstCanonicalFamily

end

end OAI
