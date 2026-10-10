import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalWeightSum
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalFixedWeightSum
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalSource
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Families (s:Input ι)(R seed:Ideal O)(ξ₁ ξ₂:RayCharacter):=
  (p:Labels s R seed)→(E:Finset (CommonIndex p.val.1 p.val.2))→
    FixedPair s.η p.val.1 p.val.2
      (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
        (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).1 E ξ₁ ξ₂

theorem original_fixed_weight_sum (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,
    ∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι)(R seed:Ideal O),
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→0<sourceRadius s→sourceRadius s≤Z^B→
    ∀(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K a₁ a₂ M:ℝ),
      0<K→0<a₁→0<a₂→
      (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
      (∀i y,V i y≠0→|y|≤M)→
    ∀(radius:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ),
      (∀p E,radius p E≤Cr*Z^L)→∀ξ₁ ξ₂:RayCharacter,∀F:Families s R seed ξ₁ ξ₂,
      sumWeight s R seed m A t W V K radius (fun p E=>(F p E).left) (fun p E=>(F p E).right)≤
        ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ))*
          (C₀*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C₀,hC₀,hbound⟩:=original_weight_sum B L Cr ε hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hbound] with Z hbound
  intro ι _ _ s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M
    hK ha₁ ha₂ hs₁ hs₂ hwin radius hr ξ₁ ξ₂ F
  exact hbound ι s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M
    fixedPresentationCost hK ha₁ ha₂ fixedPresentationCost_pos.le hs₁ hs₂ hwin radius
    (fun p E=>(F p E).left) (fun p E=>(F p E).right) hr
    (fun p E=>(F p E).conductor_caps.1) (fun p E=>(F p E).conductor_caps.2)

end SevenEighths.CenteredMomentFirstNonexceptionalFixedWeightSum

end

end OAI
