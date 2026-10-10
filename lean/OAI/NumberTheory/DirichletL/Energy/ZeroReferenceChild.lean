import OAI.NumberTheory.DirichletL.Energy.ReferenceLowChild

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReferenceChild
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyProfiles CenteredMomentLattice
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceLowChild
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentInductionEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization CenteredMomentRetainedProfile
local notation "O"=>HeckeFamily.O

lemma independent_energy {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (hB:0≤Bmask)(ha:0<a)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    (unitBudgetState s hB).plainEnergy (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂) 0 X₁ X₂:=by
  have hh:=independent_child_energy s ha W₁ W₂ hs₁ hs₂ (∅:Finset (Fin 0))
    (fun _=>∅) (fun _ _=>0) (fun _=>1) t₁ t₂ X₁ X₂ hX₁ hX₂ (by simp)
  simpa only [Finset.prod_empty,mul_one,energy,NaturalState.plainEnergy,
    CenteredMomentRetainedEnergy.positiveSlotRow,Fintype.prod_empty,
    unitBudgetState,unpuncturedState,NaturalState.mask,effectiveState,effectiveRadial] using hh

theorem independent_from_low
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤Bmask)(ha:0<a)(s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)
    (hs:s.width≤Mcap)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    (hsmall:length Z X₁+length Z X₂≤5*s.width/6):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S)^2*Z^(s.width+ε):=by
  rw [independent_energy s hB ha W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂]
  have hh:=hlow (unitBudgetState s hB) hQ hs
    (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂) 0 X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    norm_zero,add_zero,one_pow,mul_one,effectiveState,effectiveRadial] using hh

theorem reflected_from_low
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤Bmask)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)(hs:s.width≤Mcap)
    (Wshort:𝓢(ℝ,ℂ))(hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    (hsmall:length Z X₁+length Z X₂≤5*s.width/6):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((reflectionProfiles ha hlo hhi Wshort hsW j k v t).control S)^2*Z^(s.width+ε):=by
  have hh:=independent_from_low a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha s hQ hs
    (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice Wshort k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hsW k) (-2*Real.pi*v) t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  have he:((annulusSeed a b hlo hhi).profile:ℝ→ℂ)=(fun y:ℝ=>(annulus y:ℂ)):=
    funext annulusTemplate_apply
  simpa only [derivativeChoice_apply,he,reflectionProfiles] using hh

end SevenEighths.CenteredMomentEnergyZeroReferenceChild

end

end OAI
