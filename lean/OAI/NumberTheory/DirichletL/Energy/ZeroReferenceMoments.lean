import OAI.NumberTheory.DirichletL.Energy.ZeroReferenceChild
import OAI.NumberTheory.DirichletL.Energy.ReferenceLowControl

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReferenceMoments
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentEnergyZeroReferenceChild CenteredMomentEnergyReferenceLowControl
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem reflected_uniform (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
    ∀(bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)(degree:ℕ)(C:ℝ),0≤C →
    ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S C → 0≤Bmask →
    ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → s.width≤Mcap →
    ∀(Wshort:𝓢(ℝ,ℂ))(_hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
      (j k:Fin 2)(v t X₁ X₂:ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    length Z X₁+length Z X₂≤5*s.width/6 →
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(s.width+ε))*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_child_control a b ha hlo hhi S 0
  refine ⟨n,T,D,hD,?_⟩
  intro bΦ Bmask L Mcap ε Z Q degree C hC hlow hB s hQ hs
    Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  have hh:=reflected_from_low a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha hlo hhi
    s hQ hs Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  have hb:=hd Wshort hsW j k v t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hb
  have hp:0≤C*diagonalControl s.radial.profile:=mul_nonneg hC (by
    unfold diagonalControl
    positivity)
  have hz:0≤Z^(s.width+ε):=(Real.rpow_pos_of_pos (zero_lt_one.trans_le s.base_ge_one) _).le
  have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hz
  apply hh.trans
  convert hmul using 1 ; ring

end SevenEighths.CenteredMomentEnergyZeroReferenceMoments

end

end OAI
