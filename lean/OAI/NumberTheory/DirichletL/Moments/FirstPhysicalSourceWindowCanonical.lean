import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowColumns

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport RayFourExpansion IdealMobiusDivisorSum
open FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowCanonicalDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def leftWindowChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C C hC.1 s.columns) (element_supported C C hC.1 s.columns)
    (fun I=>divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta C a*leftCoefficient e r ρ (element C C hC.1 s.columns a)) χ I*
      columnPhase V (Real.log (‖eisEmbedding (element C C hC.1 s.columns I)‖^2/X)) θ) z

def rightWindowChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C D hD.1 s.columns) (element_supported C D hD.1 s.columns)
    (fun I=>divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta D a*rightCoefficient e r ρ (element C D hD.1 s.columns a)) χ I*
      star (columnPhase V (Real.log (‖eisEmbedding (element C D hD.1 s.columns I)‖^2/X)) θ)) z

theorem actual_canonical_window_integrals (η:Character)(m:O)(hm:m≠0)
    (hmLam:goodLambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let M:=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*activeConductor C D};
    ∃τ₁ τ₂:Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      ∀s:OriginalData ι,(∀i,∀I∈s.S i,I≠0)→(∀i,∀I∈s.S (Sum.inl i),Prime I)→
      s.s∣C→s.s∣D→∀t T θ X Y:ℝ,0<X→0<Y→
      ∀V₁:ℝ→ℂ,∀hV₁c:HasCompactSupport V₁,∀hV₁s:ContDiff ℝ ∞ V₁,
      ∀V₂:ℝ→ℂ,∀hV₂c:HasCompactSupport V₂,∀hV₂s:ContDiff ℝ ∞ V₂,
      ∀L:Ideal O,∀z:O,
        (Real.sqrt T:ℂ)⁻¹*leftWindowChild s η m t C D hC E ξ₁ L θ X V₁ z=
          (∫w:ℝ,columnDensity V₁ hV₁c hV₁s w*logPhase (θ-w) (Real.log X)*
            allocatedPolynomial s C L τ₁ (t+2*Real.pi*(w-θ)) T z) ∧
        (Real.sqrt T:ℂ)⁻¹*rightWindowChild s η m t C D hC hD E ξ₂ L θ Y V₂ (-z)=
          (∫w:ℝ,columnDensity (fun x=>star (V₂ x)) (conjugate_compact V₂ hV₂c)
            (conjugate_smooth V₂ hV₂s) w*logPhase (-θ-w) (Real.log Y)*
            allocatedPolynomial s D L τ₂ (t+2*Real.pi*(w-(-θ))) T (-z)):=by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩:=actual_child_family η m hm hmLam hm2 C D hC hD E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_⟩
  intro s hS hp hsC hsD t T θ X Y hX hY V₁ hV₁c hV₁s V₂ hV₂c hV₂s L z
  constructor
  · exact column_window_original_integral s hS hp C C hC.1 hC rfl hsC τ₁ t T θ X hX
      V₁ hV₁c hV₁s L _ (h₁ s.columns s.beta t L) z
  · exact column_star_window_original_integral s hS hp C D hC.1 hD hCD hsD τ₂ t T θ Y hY
      V₂ hV₂c hV₂s L _ (h₂ s.columns s.beta t L) z

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
