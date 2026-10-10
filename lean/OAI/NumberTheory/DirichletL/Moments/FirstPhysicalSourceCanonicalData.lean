import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalColumn

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceRow
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport
open CenteredMomentGaussEnergy CenteredMomentFirstColumns CenteredMomentChildAssembly
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily
open RayFourExpansion IdealMobiusDivisorSum ActualEisensteinCubic CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstCanonicalDataDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def allocatedPolynomial (s:OriginalData ι)(C L:Ideal O)(τ:Character)(t T:ℝ)(z:O):ℂ:=
  ∑B:actualAllocations s.S C,frozenCoefficient B.val C s.R s.nu s.slot s.lengths*
    gaussPolynomial Finset.univ (sourceGenerator (allocatedData s C L B).columns)
      (sourceGenerator_supported (allocatedData s C L B).columns)
      ((allocatedData s C L B).coefficient τ fixedBadMask t T) z

def leftChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C C hC.1 s.columns) (element_supported C C hC.1 s.columns)
    (divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta C a*leftCoefficient e r ρ (element C C hC.1 s.columns a)) χ) z

def rightChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C D hD.1 s.columns) (element_supported C D hD.1 s.columns)
    (divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta D a*rightCoefficient e r ρ (element C D hD.1 s.columns a)) χ) z

theorem actual_canonical_original_data (η:Character)(m:O)(hm:m≠0)
    (hmLam:goodLambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let M:=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*activeConductor C D};
    ∃τ₁ τ₂:Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      ∀s:OriginalData ι,(∀i,∀I∈s.S i,I≠0)→(∀i,∀I∈s.S (Sum.inl i),Prime I)→
      s.s∣C→s.s∣D→∀t T:ℝ,∀L:Ideal O,∀z:O,
        (Real.sqrt T:ℂ)⁻¹*leftChild s η m t C D hC E ξ₁ L z=
          allocatedPolynomial s C L τ₁ t T z ∧
        (Real.sqrt T:ℂ)⁻¹*rightChild s η m t C D hC hD E ξ₂ L (-z)=
          allocatedPolynomial s D L τ₂ t T (-z):=by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩:=actual_child_family η m hm hmLam hm2 C D hC hD E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_⟩
  intro s hS hp hsC hsD t T L z
  constructor
  · exact first_column_original_data s hS hp C hC hsC τ₁ t T L _
      (h₁ s.columns s.beta t L) z
  · exact first_column_original_data_filter s hS hp C D hC.1 hD hCD hsD τ₂ t T L _
      (h₂ s.columns s.beta t L) (-z)

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
