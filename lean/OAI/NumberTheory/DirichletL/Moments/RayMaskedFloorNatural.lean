import OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSlots
import OAI.NumberTheory.DirichletL.Moments.PlainPositiveEnergy
import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalRadial

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_pair_slots {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ),Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ → ∀A : Finset α,A⊆F →
      radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
        polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
        ∏i∈A,naturalSlot (naturalCharacter η z) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
        r.keep r.profile r.scale ≤
      C*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  obtain ⟨J,Cs,hCs,hslot⟩ := natural_slot_product M H hH F W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  obtain ⟨S,Cp,hCp,hplain⟩ := global_positive_scale a₀ b₀ ha₀
  refine ⟨J,S,Cp^4*3^8*Cs,by positivity,?_⟩
  intro η₀
  filter_upwards [hslot η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ A hAF
  let E := Cs*(1+|t|+T)^J*Z^(loss+κ*(∑i∈F,w i))
  have hE : 0≤E := by dsimp [E]; positivity
  let B₁ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁ : 0≤B₁ := apply_nonneg _ _
  have hB₂ : 0≤B₂ := apply_nonneg _ _
  let B := Cp^2*(B₁*B₂)*Qbound^2*3^4*Real.sqrt E
  have hB : 0≤B := by dsimp [B]; positivity
  have hpoint (z : O) (hkeep : r.keep z) :
      ‖polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
        polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
        ∏i∈A,naturalSlot (naturalCharacter η z) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖≤B := by
    have hn := hz z hkeep
    have heq := naturalCharacter_eq η z hn
    have hnon : (naturalCharacter η z).residue≠1 := by
      rw [heq]
      exact CenteredMomentNonprincipalGate.actual_row_nonprincipal η
        (naturalRow η z hn).character (internalQ Q η₀) fixedBadMask 1 z
        (by simpa only [one_mul] using (naturalRow η z hn).element) (hex z hkeep)
    have h₁ : ‖polynomial (naturalCharacter η z) false W₁ X₁ 0 0‖≤Cp*B₁*Qbound*3^2 := by
      have he := hplain W₁ hs₁ _ hnon X₁ 0 hX₁
      norm_num only [abs_zero,add_zero] at he
      apply he.trans
      simpa only [show (3:ℝ)^2=9 by norm_num] using (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hQ z hkeep) (mul_nonneg hCp.le hB₁)) (show (0:ℝ)≤9 by norm_num))
    have h₂ : ‖polynomial (naturalCharacter η z) false W₂ X₂ 0 0‖≤Cp*B₂*Qbound*3^2 := by
      have he := hplain W₂ hs₂ _ hnon X₂ 0 hX₂
      norm_num only [abs_zero,add_zero] at he
      apply he.trans
      simpa only [show (3:ℝ)^2=9 by norm_num] using (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hQ z hkeep) (mul_nonneg hCp.le hB₂)) (show (0:ℝ)≤9 by norm_num))
    have hs := hZ θ w σ v t T hw hwL hσlo hσhi hT hv η z hn (naturalRow η z hn)
      (by simpa only [heq] using hmod z hkeep) Q hQM (hex z hkeep) A hAF
    rw [←heq] at hs
    have hsroot := (Real.le_sqrt (norm_nonneg _) hE).mpr hs
    rw [norm_mul,norm_mul]
    apply (mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity))
      hsroot (norm_nonneg _) (by positivity)).trans_eq
    dsimp [B,B₁,B₂]
    norm_num only [abs_zero,add_zero]
    ring
  have he := radial_bound_on_keep _ r B hB hpoint
  apply he.trans_eq
  dsimp [B,E,B₁,B₂]
  rw [mul_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt hE]
  ring

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
