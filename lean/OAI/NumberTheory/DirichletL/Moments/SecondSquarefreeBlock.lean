import OAI.NumberTheory.DirichletL.Moments.SecondRadicalBlock
import OAI.NumberTheory.DirichletL.Moments.SourceAbsoluteEnvelope
import OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell
import OAI.NumberTheory.DirichletL.Moments.SecondMaskedWindow
import OAI.NumberTheory.DirichletL.Moments.SecondRadicalColumns
import OAI.NumberTheory.DirichletL.Moments.SecondWindowBudget

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondSquarefreeBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

theorem actual_block_from_squarefree_source (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃B:ℝ,0≤B ∧ ∀r:ℝ,0<r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
        (C D:Ideal O) (hC:Supported C) (hD:Supported D),
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0<X → 0<Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),0<H →
      (∀z:O,0≤(Φ (normValue z/H)).re) → (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:Ideal O→ℝ,
      (∀L,0≤E₁ L) → (∀L,0≤E₂ L) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool C hC.1 S)
          (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤E₁ L*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool D hD.1 S)
          (fun I=>if IsCoprime D I ∧ L∣I then β (D*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤E₂ L*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        B*∑L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (windowBudget J₁ t (E₁ L)*windowBudget J₂ t (E₂ L)) := by
  obtain ⟨B,hB,hbound⟩:=CenteredMomentSecondRadicalBlock.actual_block_from_masked_source W decay J₁ J₂
  refine ⟨B,hB,?_⟩
  intro r hr η τ t S β C D hC hD hCD U A hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  let coarse (G:Ideal O) (hg:G≠0) (L:Ideal O):ℝ:=
    QuadraticInitialBound.diagonalControl Φ*max 1 H*
      (∑I∈residualPool G hg S,‖if IsCoprime G I ∧ L∣I then β (G*I) else 0‖)^2
  have hcoarse (G:Ideal O) (hg:G≠0) (L:Ideal O):0≤coarse G hg L:=
    mul_nonneg (mul_nonneg (QuadraticInitialBound.diagonalControl_nonneg Φ) (by positivity)) (sq_nonneg _)
  let F₁:Ideal O→ℝ:=fun L=>if Squarefree L then E₁ L else coarse C hC.1 L
  let F₂:Ideal O→ℝ:=fun L=>if Squarefree L then E₂ L else coarse D hD.1 L
  have hF₁ (L:Ideal O):0≤F₁ L:=by dsimp [F₁];split_ifs;exact hE₁ L;exact hcoarse C hC.1 L
  have hF₂ (L:Ideal O):0≤F₂ L:=by dsimp [F₂];split_ifs;exact hE₂ L;exact hcoarse D hD.1 L
  have hsource (G:Ideal O) (hg:G≠0) (L:Ideal O) (χ:RayCharacter) (v:ℝ) (J:ℕ):
      sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool G hg S)
        (fun I=>if IsCoprime G I ∧ L∣I then β (G*I) else 0)
        (heightCoeff (τ χ) v) Φ H≤coarse G hg L*(1+‖v‖)^(2*J):=by
    have hh:=CenteredMomentSourceAbsoluteEnvelope.actual_source_absolute (residualPool G hg S)
      (fun I=>if IsCoprime G I ∧ L∣I then β (G*I) else 0) (τ χ) v
      (nonexceptional η χ Q m A) Φ H hH
    apply hh.trans
    exact le_mul_of_one_le_right (hcoarse G hg L) (one_le_pow₀ (by linarith [norm_nonneg v]))
  have hh:=hbound r hr η τ t S β C D hC hD hCD U hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor F₁ F₂ hF₁ hF₂
    (by
      intro L hL χ v
      by_cases hs:Squarefree L
      · simpa only [F₁,ite_eq_left hs] using hleft L hL hs χ v
      · simpa only [F₁,ite_eq_right hs] using hsource C hC.1 L χ v J₁)
    (by
      intro L hL χ v
      by_cases hs:Squarefree L
      · simpa only [F₂,ite_eq_left hs] using hright L hL hs χ v
      · simpa only [F₂,ite_eq_right hs] using hsource D hD.1 L χ v J₂)
  apply hh.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro L hL
  by_cases hμ:(UniqueFactorizationMonoid.moebius L:ℂ)=0
  · simp only [hμ,norm_zero,zero_mul]
  · have hs:=CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hμ
    simp only [F₁,F₂,ite_eq_left hs]

end SevenEighths.CenteredMomentSecondSquarefreeBlock

end

end OAI
