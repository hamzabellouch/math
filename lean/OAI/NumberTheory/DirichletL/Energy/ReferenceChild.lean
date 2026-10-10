import OAI.NumberTheory.DirichletL.Energy.ReferenceReflection
import OAI.NumberTheory.DirichletL.Energy.AllocatedChildren
import OAI.NumberTheory.DirichletL.Energy.SlotHeight
import OAI.NumberTheory.DirichletL.Energy.Profiles

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceChild
open HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergySlotHeight
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentEnergyProfiles CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentLattice CenteredMomentRetainedProfile CenteredMomentTwist
local notation "O"=>HeckeFamily.O

def unpuncturedState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):NaturalState Z 0 bΦ where
  character:=s.character
  fixedModulus:=s.fixedModulus
  puncture:=1
  radial:=(effectiveState s).radial
  rowWidth:=s.rowWidth
  characterWidth:=s.characterWidth
  base_ge_one:=s.base_ge_one
  row_nonneg:=s.row_nonneg
  character_nonneg:=s.character_nonneg
  scale_eq:=s.scale_eq
  modulus_bound:=s.modulus_bound
  puncture_ne_zero:=one_ne_zero
  puncture_bound:=by simp
  radial_support:=s.radial_support
  row_ne_zero:=fun z hz=>s.row_ne_zero z hz.1
  nonexceptional:=by
    intro z hz hh
    have hn:=s.row_ne_zero z hz.1
    have hunit:CenteredExceptionalProfile.FixedInducingRow s.character s.fixedModulus fixedBadMask 1 z:=
      (CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff s.character s.fixedModulus
        fixedBadMask (idealGenerator 1) 1 z fixedBadMask_ne_zero
        (idealGenerator_ne_zero 1 one_ne_zero) one_ne_zero hn
        (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hh
    exact s.nonexceptional z hz.1
      ((CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff s.character s.fixedModulus
        fixedBadMask (idealGenerator s.puncture) 1 z fixedBadMask_ne_zero
        (idealGenerator_ne_zero _ s.puncture_ne_zero) one_ne_zero hn
        (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hunit)

lemma unpunctured_width {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):
    (unpuncturedState s).width=s.width:=rfl

def independentProfiles {a b:ℝ}(ha:0<a)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)(t₁ t₂:ℝ):Profiles a b where
  profile:=fun i=>if i=0 then normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
    else normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  support:=by
    intro i
    split_ifs
    · exact (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁
    · exact (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂

theorem independent_child_energy {α:Type*}[Fintype α][DecidableEq α]
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(ha:0<a)
    (W₁ W₂:𝓢(ℝ,ℂ))(hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i∈F,0<P i):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁ *
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂ *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    energy (unpuncturedState s).character (unpuncturedState s).mask 1 0
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 0)
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 1)
      (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂
      (unpuncturedState s).radial.keep (unpuncturedState s).radial.profile (unpuncturedState s).radial.scale:=by
  have hh:=natural_subset_radial_eq_energy s.character (effectiveState s).radial
    (fun z hz=>s.row_ne_zero z hz.1) F
    (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
    (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂)
    pool β P X₁ X₂ hX₁ hX₂ hP
  simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t₁,
    CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t₂] at hh
  simpa only [independentProfiles,unpuncturedState,NaturalState.mask,
    show (1:Fin 2)≠0 by decide,ite_false,ite_true,effectiveState,effectiveRadial] using hh

theorem independent_child_ray_energy {α:Type*}[Fintype α][DecidableEq α]
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(ha:0<a)
    (W₁ W₂:𝓢(ℝ,ℂ))(hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→Finset (Ideal O))(ν:α→Character)(W:α→ℝ→ℂ)(P σ freq:α→ℝ)
    (hp:∀i∈F,∀I∈pool i,Prime I)(hP:∀i∈F,0<P i)
    (t t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁ *
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂ *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (fun I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I) t) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    energy (unpuncturedState s).character (unpuncturedState s).mask 1 0
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 0)
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 1)
      (fun i:F=>pool i)
      (fun (i:F) I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (t+freq i) I)
      (fun i:F=>P i) X₁ X₂
      (unpuncturedState s).radial.keep (unpuncturedState s).radial.profile (unpuncturedState s).radial.scale:=by
  rw [independent_child_energy s ha W₁ W₂ hs₁ hs₂ F pool _ P t₁ t₂ X₁ X₂ hX₁ hX₂ hP]
  exact inherited_height_energy _ _ _ _ _ (fun i:F=>pool i)
    (fun (i:F) I=>idealCoeff (ν i) I) (fun i:F=>W i)
    (fun i:F=>P i) (fun i:F=>σ i) (fun i:F=>freq i)
    (fun i=>hP i i.property) (fun i I hI=>(hp i i.property I hI).ne_zero)
    t 0 X₁ X₂ _ _ _

end SevenEighths.CenteredMomentEnergyReferenceChild

end

end OAI
