import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalWindow
import OAI.NumberTheory.DirichletL.Moments.SecondCanonicalScalar
import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptional

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondIdealBlockBound
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem logAnnulus_enclosure (x : ℝ) (hx : logAnnulus x≠0) : |x|≤Real.log 4 := by
  have hh := logAnnulus_support hx
  exact abs_le.mpr ⟨hh.1,hh.2.trans (Real.log_nonneg (by norm_num))⟩

theorem actual_nonexceptional_block_bound (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ B : ℝ,0≤B ∧ ∀ r : ℝ,0<r →
      ∀ (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
        (C D : Ideal O) (hC : Supported C) (hD : Supported D),
      primeSupport C=primeSupport D →
      ∀ (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
        (ρ x : O→ℝ) (u : sectorPool C hC.1 S→ℝ) (v : sectorPool D hD.1 S→ℝ)
        (Q : Ideal O) (m : O) (χ₀ : RayCharacter),
      Q≤Ideal.span {(72:O)} → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let c := fun I : sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I
      let d := fun J : sectorPool D hD.1 S=>β (D*J)*heightCoeff η t J
      (∀ z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀ (Φ : 𝓢(ℝ,ℂ)) (H : ℝ),0<H →
      (∀ z : O,0≤(Φ (normValue z/H)).re) →
      (∀ z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀ E₁ E₂ : Ideal O→ℝ,
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),0≤E₁ L) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),0≤E₂ L) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),∀ χ : RayCharacter,∀ w : ℝ,
        restrictedEnergy (nonexceptional η χ Q m A) Finset.univ (sectorElement C hC.1 S)
          (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
            (movingCoefficient A (sectorElement C hC.1 S) c) χ I*columnPhase logAnnulus (u I) w) Φ H≤
              (E₁ L*(1+‖w‖)^J₁)^2) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),∀ χ : RayCharacter,∀ w : ℝ,
        restrictedEnergy (nonexceptional η χ Q m A) Finset.univ (sectorElement D hD.1 S)
          (fun J=>divisorCoefficient L (sectorElement D hD.1 S)
            (movingCoefficient A (sectorElement D hD.1 S) d) χ J*star (columnPhase logAnnulus (v J) w)) Φ H≤
              (E₂ L*(1+‖w‖)^J₂)^2) →
      (1+r)^decay*‖∑ z∈rows,retainedScalar C D U R z*
        ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            (c I*star (d J))*wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z) (u I) (v J)‖≤
        B*∑ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(E₁ L*E₂ L) := by
  obtain ⟨B,hB,hbound⟩ := whole_kernel_nonexceptional_second_bound W (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num)) (fun _ x hx=>logAnnulus_enclosure x hx)
    decay J₁ J₂
  refine ⟨B,hB,?_⟩
  intro r hr η t S β C D hC hD hCD U R rows ρ x u v Q m χ₀ hQ hmLam hm2
  dsimp only
  intro hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hcopD (J : sectorPool D hD.1 S) :
      IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement D hD.1 S J) := by
    simpa only [mul_comm] using sectorElement_coprime D C hD hC hCD.symm S J
  have he := hbound r hr rows Finset.univ Finset.univ (primaryGenerator C) (primaryGenerator D)
    (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
    (sectorElement C hC.1 S) (sectorElement D hD.1 S)
    ((supported_span_primaryGenerator_iff C).mpr hC) ((supported_span_primaryGenerator_iff D).mpr hD)
    (sectorElement_supported C hC.1 S) (sectorElement_supported D hD.1 S)
    (primaryGenerator_spec C (supported_primaryGenerator_ne_zero C hC)).2
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary D hD.1 S)
    (sectorElement_coprime C D hC hD hCD S) hcopD
    (retainedScalar C D U R) (fun I=>β (C*I)*heightCoeff η t I)
    (fun J=>β (D*J)*heightCoeff η t J) u v ρ x η χ₀ Q m hQ hmLam hm2 hrows
    (fun z _=>actual_retained_scalar_norm C D hC hD hCD U R z)
    (fun z _=>logAnnulus_norm _) (fun z _=>logAnnulus_norm _)
    Φ H hH (by simpa only [normValue_eq_embedding] using hΦ)
    (by simpa only [normValue_eq_embedding] using hmajor) E₁ E₂
    (by simpa only [sectorElement_span] using hE₁) (by simpa only [sectorElement_span] using hE₂)
    (by simpa only [sectorElement_span] using hleft) (by simpa only [sectorElement_span] using hright)
  have hcop (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      IsCoprime (sectorElement C hC.1 S I) (sectorElement D hD.1 S J) ↔
        IsCoprime (I:Ideal O) (J:Ideal O) := by
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  simp_rw [hcop,sectorElement_span] at he
  simpa only [idealCorrelation,primaryGenerator_mul,sectorElement] using he

end SevenEighths.CenteredMomentSecondIdealBlockBound

end

end OAI
