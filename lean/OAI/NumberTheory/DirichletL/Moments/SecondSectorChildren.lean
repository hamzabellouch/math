import OAI.NumberTheory.DirichletL.Moments.SecondSectorColumns
import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily CenteredMomentSupport
open CenteredMomentSecondScaled CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentFixedRay CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem sector_correlation_children (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (A₀ : O) (rows : Finset O) (q : O → ℂ) (K : O → Ideal O → Ideal O → ℂ) :
    let a := sectorElement C hC.1 S
    let b := sectorElement D hD.1 S
    let c := fun I : sectorPool C hC.1 S => β (C*I)*heightCoeff η t I
    let d := fun J : sectorPool D hD.1 S => β (D*J)*heightCoeff η t J
    (∑ z∈rows,q z*∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        idealCorrelation (C*I) (D*J)
          ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
          ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A₀*z)
        else 0)*(c I*star (d J))*K z I J)=
      ∑ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S => (J:Ideal O)),
        (UniqueFactorizationMonoid.moebius L:ℂ)*
          ∑ χ : RayCharacter,∑ ξ : RayCharacter,
            pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ*
              ∑ z∈rows,(q z*idealCorrelation C D hC hD (A₀*z))*
                ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
                  ((divisorCoefficient L a (movingCoefficient A₀ a c) χ I*idealRowHom z I)*
                    star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) J*idealRowHom (-z) J))*K z I J := by
  dsimp only
  have hb (J : sectorPool D hD.1 S) :
      IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement D hD.1 S J) := by
    simpa only [mul_comm] using sectorElement_coprime D C hD hC hCD.symm S J
  have he := actual_scaled_row_children rows Finset.univ Finset.univ
    (primaryGenerator C) (primaryGenerator D) A₀
    (sectorElement C hC.1 S) (sectorElement D hD.1 S)
    ((supported_span_primaryGenerator_iff C).mpr hC) ((supported_span_primaryGenerator_iff D).mpr hD)
    (sectorElement_supported C hC.1 S) (sectorElement_supported D hD.1 S)
    (primaryGenerator_spec C (supported_primaryGenerator_ne_zero C hC)).2
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary D hD.1 S)
    (sectorElement_coprime C D hC hD hCD S) hb q
    (fun I => β (C*I)*heightCoeff η t I) (fun J => β (D*J)*heightCoeff η t J)
    (fun z I J => K z I J)
  have hcop (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      IsCoprime (sectorElement C hC.1 S I) (sectorElement D hD.1 S J) ↔ IsCoprime (I:Ideal O) (J:Ideal O) := by
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  simp_rw [hcop,sectorElement_span] at he
  simpa only [idealCorrelation,primaryGenerator_mul,sectorElement] using he

end SevenEighths.CenteredMomentSecondSectorChildren

end

end OAI
