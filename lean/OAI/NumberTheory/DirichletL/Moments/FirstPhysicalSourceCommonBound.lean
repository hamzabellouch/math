import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedEnergy
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceBound
import OAI.NumberTheory.DirichletL.Moments.SecondIdealBlockBound

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSecondIdealBlockBound
local notation "O"=>ActualEisensteinCubic.O
universe u

theorem fixed_log_block_from_common_energy (W:𝓢(ℝ,ℂ))(decay J₁ J₂:ℕ):
    ∃Cbound:ℝ,0≤Cbound ∧ ∀{ι:Type u}[Fintype ι],∀η:Character,∀s:OriginalData ι,
    ∀t:ℝ,∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(E:Finset (CommonIndex C D))(rows:Finset O),(∀h∈rows,h≠0)→
    ∀K K₀ H₀ A₀ B₀:ℝ,0<K→0<K₀→0<H₀→0<A₀→0<B₀→
    ∀(U:𝓢(ℝ,ℂ))(H:ℝ),0<H→
    (∀h:O,0≤(U (‖eisEmbedding h‖^2/H)).re)→
    (∀h∈rows,1≤(U (‖eisEmbedding h‖^2/H)).re)→
    ∀E₁ E₂:Ideal O→ℝ,
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}),0≤E₁ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}),0≤E₂ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}),∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L U H).re≤E₁ L*(1+‖v‖)^(2*J₁))→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}),∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L U H).re≤E₂ L*(1+‖v‖)^(2*J₂))→
    (1+K₀*H₀/(A₀*B₀))^decay*
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K K₀ H₀ A₀ B₀‖≤
      ‖scalar C D hC E K A₀ B₀‖*Cbound*
        ∑L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (windowBudget J₁ t (E₁ L)*windowBudget J₂ t (E₂ L)):=by
  obtain ⟨Cb,hCb,hbound⟩:=physical_block_child_bound W (fun _=>logAnnulus) (fun _=>Real.log 4)
    (fun _=>Real.log_nonneg (by norm_num)) (fun _ _ hn=>logAnnulus_enclosure _ hn) decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows hrows K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
    U H hH hU hmajor E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound η (fixedBadMask*idealGenerator s.R) t s.columns s.beta C D hC hD hCD E rows hrows
    K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
    (fun _ _=>logAnnulus_norm _) (fun _ _=>logAnnulus_norm _) U H hH hU hmajor
    (fun L=>windowBudget J₁ t (E₁ L)) (fun L=>windowBudget J₂ t (E₂ L))
    (fun L _=>windowBudget_nonneg _ _ _) (fun L _=>windowBudget_nonneg _ _ _)
  · intro L hL χ θ
    exact (fixedPair η C D hC E χ χ).left_window_energy s t θ A₀ hA₀ L U H hH hU J₁ (E₁ L)
      (hE₁ L hL) (hleft L hL χ)
  · intro L hL χ θ
    exact (fixedPair η C D hC E χ χ).right_window_energy hD hCD s t θ B₀ hB₀ L U H hH hU J₂ (E₂ L)
      (hE₂ L hL) (hright L hL χ)

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
