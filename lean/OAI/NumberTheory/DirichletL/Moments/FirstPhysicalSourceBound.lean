import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSource

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentFirstReduced
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentFirstChildBound CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentSmooth RayFourExpansion IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem physical_block_child_bound (W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (M:Fin 4→ℝ)(hM:∀i,0≤M i)(hV:∀i y,V i y≠0→|y|≤M i)(A J₁ J₂:ℕ):
    ∃Cbound:ℝ,0≤Cbound ∧
    ∀(η:Character)(m:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
      (C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(E:Finset (CommonIndex C D))(rows:Finset O),(∀h∈rows,h≠0)→
    ∀K K₀ H₀ A₀ B₀:ℝ,0<K→0<K₀→0<H₀→0<A₀→0<B₀→
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let k:=K/‖eisEmbedding e‖^2;
    let r:=activeConductor C D;
    let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D);
    (∀h∈rows,‖V 0 (Real.log ((k/‖eisEmbedding r‖^2)/K₀))‖≤1)→
    (∀h∈rows,‖V 1 (Real.log (‖eisEmbedding h‖^2/H₀))‖≤1)→
    ∀(U:𝓢(ℝ,ℂ))(H:ℝ),0<H→
    (∀h:O,0≤(U (‖eisEmbedding h‖^2/H)).re)→
    (∀h∈rows,1≤(U (‖eisEmbedding h‖^2/H)).re)→
    ∀B₁ B₂:Ideal O→ℝ,
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=>Ideal.span {element C D hD.1 S b}),0≤B₁ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=>Ideal.span {element C D hD.1 S b}),0≤B₂ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=>Ideal.span {element C D hD.1 S b}),∀χ:RayCharacter,∀v:ℝ,
      (gaussEnergy Finset.univ (element C C hC.1 S) (element_supported C C hC.1 S)
        (fun a=>divisorCoefficient L (element C C hC.1 S)
          (fun a=>coefficient η m 1 t c C a*leftCoefficient e r ρ (element C C hC.1 S a)) χ a*
          columnPhase (V 2) (Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀)) v) U H).re
            ≤(B₁ L*(1+‖v‖)^J₁)^2)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=>Ideal.span {element C D hD.1 S b}),∀χ:RayCharacter,∀v:ℝ,
      (gaussEnergy Finset.univ (element C D hD.1 S) (element_supported C D hD.1 S)
        (fun b=>divisorCoefficient L (element C D hD.1 S)
          (fun b=>coefficient η m 1 t c D b*rightCoefficient e r ρ (element C D hD.1 S b)) χ b*
          star (columnPhase (V 3) (Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀)) v)) U H).re
            ≤(B₂ L*(1+‖v‖)^J₂)^2)→
    (1+K₀*H₀/(A₀*B₀))^A*‖block η m 1 t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀‖≤
      ‖scalar C D hC E K A₀ B₀‖*Cbound*
        ∑L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
          (fun b=>Ideal.span {element C D hD.1 S b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(B₁ L*B₂ L):=by
  obtain ⟨Cbound,hCbound,hbound⟩:=whole_kernel_first_child_bound.{0,0} W V M hM hV A J₁ J₂
  refine ⟨Cbound,hCbound,?_⟩
  intro η m t S c C D hC hD hCD E rows hrows K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
  dsimp only
  intro hV₀ hV₁ U H hH hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  have hh:=hbound (K₀*H₀/(A₀*B₀)) (div_pos (mul_pos hK₀ hH₀) (mul_pos hA₀ hB₀))
    rows Finset.univ Finset.univ (element C C hC.1 S) (element C D hD.1 S)
    (element_supported C C hC.1 S) (element_supported C D hD.1 S)
    (element_primary C C hC.1 S) (element_primary C D hD.1 S)
    (fun a=>coefficient η m 1 t c C a) (fun b=>coefficient η m 1 t c D b)
    (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E) (activeConductor C D)
    (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D))
    (finiteSexticRow_mul _ _ _) (QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ _)
    (fun h=>star (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D) h))
    (fun a=>Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀))
    (fun b=>Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀))
    (fun _=>Real.log ((K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2/
      ‖eisEmbedding (activeConductor C D)‖^2)/K₀))
    (fun h=>Real.log (‖eisEmbedding h‖^2/H₀))
    (fun h _=>by rw [norm_star];exact QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ _)
    hV₀ hV₁ U H hH hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [block_eq_whole η m 1 t S c C D hC hD hCD E rows hrows W V K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀,
    norm_mul]
  convert mul_le_mul_of_nonneg_left hh (norm_nonneg (scalar C D hC E K A₀ B₀)) using 1 <;> ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
