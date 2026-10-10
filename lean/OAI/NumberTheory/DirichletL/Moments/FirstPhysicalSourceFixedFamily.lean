import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourcePresentation
import OAI.NumberTheory.DirichletL.Moments.FirstMaskedFamily
import OAI.NumberTheory.DirichletL.Moments.SupportedZeroEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy CenteredMomentCommonSupport
open CenteredMomentChildAssembly CenteredMomentAddedZeroUniform RayFourExpansion CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

structure FixedPair (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter) where
  left : Character
  right : Character
  left_modulus : left.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}
  right_modulus : right.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}
  left_height : ∀I:Ideal O,Supported I→∀t:ℝ,
    heightCoeff left t I=rowWeight η fixedBadMask 1 1 t I*
      (leftCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))
  right_height : ∀I:Ideal O,Supported I→∀t:ℝ,
    heightCoeff right t I=rowWeight η fixedBadMask 1 1 t I*
      (rightCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))

def fixedPair (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter):FixedPair η C D hC E ξ₁ ξ₂:=
  Classical.choice (by
    obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,_,_⟩:=exists_canonical_masked_pair η C D hC E ξ₁ ξ₂
    exact ⟨⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩⟩)

theorem FixedPair.conductor_caps {η:Character}{C D:Ideal O}{hC:Supported C}
    {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}(F:FixedPair η C D hC E ξ₁ ξ₂):
    (F.left.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2 ∧
    (F.right.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=
  fixed_pair_presentation_caps η F.left F.right C D E F.left_modulus F.right_modulus

variable {ι:Type*}[Fintype ι]
local instance firstFixedFamilyDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem beta_coprime (s:OriginalData ι)(I:Ideal O)(h:s.beta I≠0):IsCoprime I s.R:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.S) s.profile I h
  rw [←he]
  by_contra hn
  apply hv0
  simp only [OriginalData.profile,profileCoefficient,hn,ite_false,mul_zero,zero_mul]

lemma extracted_mask_redundant (s:OriginalData ι)(C:Ideal O):
    maskedSource (idealGenerator s.R) (fun I=>s.beta (C*I))=(fun I=>s.beta (C*I)):=by
  apply maskedSource_eq_of_live
  intro I hI
  rw [span_idealGenerator]
  exact (beta_coprime s (C*I) hI).of_mul_left_right

theorem fixed_divisor_column (s:OriginalData ι)(η τ:Character)(C:Ideal O)
    (F:O→ℂ)(ξ:RayCharacter)
    (hτ:∀I:Ideal O,Supported I→∀t:ℝ,heightCoeff τ t I=
      rowWeight η fixedBadMask 1 1 t I*(F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (L I:Ideal O)(hI:Supported I)(t:ℝ):
    divisorCoefficient L (fun J:Ideal O=>primaryGenerator J)
      (fun J=>s.beta (C*J)*rowWeight η (fixedBadMask*idealGenerator s.R) 1 1 t J*
        F (primaryGenerator J)) ξ I=
      (if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I:=by
  have hh:=divisor_column_masked η τ F ξ hτ (idealGenerator s.R) L I hI (fun J=>s.beta (C*J)) t
  rw [extracted_mask_redundant] at hh
  exact hh

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
