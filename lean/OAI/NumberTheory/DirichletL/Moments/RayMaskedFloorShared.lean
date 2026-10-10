import OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorNatural
import OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorCoefficients
import OAI.NumberTheory.DirichletL.Moments.PlainPositiveEnergy
import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalRadial

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem masked_natural_pair_slots {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ)(R : Ideal O),R≠0 → Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      radialEnergy (fun z=>polynomial (excluded (naturalCharacter η z) R) false W₁ X₁ 0 0*
        polynomial (excluded (naturalCharacter η z) R) false W₂ X₂ 0 0*
        ∏i∈F,naturalSlot (excluded (naturalCharacter η z) R) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
        r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := natural_pair_slots M H hH F W a b ha hWs hW a₀ b₀ ha₀
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  obtain ⟨B,hB,hcoeff⟩ := slot_coefficient_bounds W a b lo hi ha hWs hW.continuous
  obtain ⟨Cd,hCd,hdelete⟩ := CenteredMomentCommonMaskRadialEnergy.actual_radial_shared_energy
    F (fun _=>b) (fun _=>B) (fun _ _=>hB.le) ε hε
  refine ⟨J,S,Cd*C,mul_pos hCd hC,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound R hR hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  let E := C*diagonalControl r.profile*max 1 r.scale*
    ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
      (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
      (1+|t|+T)^J*Z^(loss+κ*(∑i∈F,w i))
  have hd := diagonalControl_nonneg r.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have hp (i : α) (hi : i∈F) (I : Ideal O) (hI : I∈primePool M H b (Z^(w i))) : Prime I :=
    (Finset.mem_filter.mp hI).2.1
  have hc (i : α) (hi : i∈F) (I : Ideal O) (hI : I∈primePool M H b (Z^(w i))) :=
    hcoeff (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (v i) t
      (Real.rpow_pos_of_pos hZ0 _) (hσlo i hi) (hσhi i hi) I (hp i hi I hI).ne_zero
  have he := hdelete (CompletedGauss.primeSupport R) (support_prime R) (naturalCharacter η)
    W₁ W₂ X₁ X₂ a₀ b₀ a₀ b₀ (fun i=>primePool M H b (Z^(w i)))
    (fun i=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t)
    (fun i=>Z^(w i)) r.keep r.profile r.scale E hX₁ hX₂ hb₀ hb₀ hs₁ hs₂ hp
    (fun _ _=>Real.rpow_pos_of_pos hZ0 _) (fun i hi I hI=>(hc i hi I hI).1)
    (fun i hi I hI=>(hc i hi I hI).2) r.scale_pos r.nonneg hE ?_
  · rw [primeSupport_product_radical R hR] at he
    exact he.trans_eq (by dsimp [E]; ring)
  · intro D₁ hD₁ D₂ hD₂ A hA
    have hn (D : Finset (Ideal O)) (hD : D∈(CompletedGauss.primeSupport R).powerset) :
        0<(Ideal.absNorm (∏I∈D,I):ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun I hi=>(support_prime R I (Finset.mem_powerset.mp hD hi)).ne_zero)))
    exact hZ θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound hQM hQbound hz hex hmod hQ
      W₁ W₂ hs₁ hs₂ _ _ (div_pos hX₁ (hn D₁ hD₁)) (div_pos hX₂ (hn D₂ hD₂))
      (F\A) Finset.sdiff_subset

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
