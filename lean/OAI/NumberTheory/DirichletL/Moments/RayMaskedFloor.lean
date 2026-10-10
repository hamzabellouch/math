import OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSource

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

theorem natural_masked_positive_floor {α : Type*} [Fintype α] [DecidableEq α] (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (L Lslot loss lo hi κ bΦ : ℝ) (hL : 0≤L) (hbΦ : 0≤bΦ) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) →
      (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤T → (∀i,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(R : Ideal O),R≠0 → Q≤M →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z) →
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
    ∀(m q ρ : ℝ),0≤m → 0≤q → m+q≤ρ → ρ≤L → r.scale=Z^m →
      (η.modulus.absNorm:ℝ)≤Z^q →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      CenteredMomentInductionEnergy.energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t
        W₁ W₂ (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*bΦ^4*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*
         (1+|t|+T)^degree*Z^(m+4*ρ+loss+κ*(∑i,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := original_masked_positive_floor (α:=α) M H hH W a b ha hWs hW
    a₀ b₀ ε ha₀ hb₀ hε (L+1) Lslot loss lo hi κ (by linarith) hLs hloss hbeta hκ
  let Fc : ℝ := fixedConductorFactor
  have hFc : 0<Fc := by
    unfold Fc fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
  refine ⟨J,S,C*Fc^4,by positivity,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_ge_atTop (Fc*bΦ),eventually_ge_atTop (1:ℝ)] with Z hZ hconst hZ1
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r R hR hQM hz hex hsΦ
    m q ρ hm hq hρ hρL hscale hη W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ1
  let r' : Radial := {r with keep := fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}
  have hmod (z : O) (hk : r'.keep z) :
      ((naturalCharacter η z).modulus.absNorm:ℝ)≤Fc*bΦ*Z^ρ := by
    have hn := hz z hk.1
    rw [naturalCharacter_eq η z hn]
    have hrow : ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^m := by
      rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←hscale]
      exact (div_le_iff₀ r.scale_pos).mp (hsΦ hk.2)
    have he := (naturalRow η z hn).modulus_power_bound Z q m bΦ hZ0 hbΦ hη hrow
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hFc.le hbΦ)
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hcap (z : O) (hk : r'.keep z) :
      ((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^(L+1) := by
    apply (hmod z hk).trans
    calc
      _ ≤ Z*Z^L := mul_le_mul hconst (Real.rpow_le_rpow_of_exponent_le hZ1 hρL)
        (Real.rpow_nonneg hZ0.le _) hZ0.le
      _ = _ := by rw [Real.rpow_add hZ0,Real.rpow_one]; ring
  have he := hZ θ w σ v t T hw hwL hσlo hσhi hT hv η Q r'
    (Fc*bΦ*Z^ρ) R hR hQM (by positivity) (fun z hk=>hz z hk.1)
    (fun z hk=>hex z hk.1) hcap hmod W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hid : CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r'.keep r'.profile r'.scale =
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale := by
    unfold CenteredMomentInductionEnergy.energy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · by_cases hp : r.profile (‖eisEmbedding z‖^2/r.scale)=0
      · simp [r',hk,hp]
      · simp [r',hk,hp]
    · simp [r',hk]
  rw [hid] at he
  dsimp only [r'] at he
  rw [hscale,max_eq_right (Real.one_le_rpow hZ1 hm)] at he
  rw [hscale]
  apply he.trans_eq
  have hzpow : Z^m*(Z^ρ)^4*Z^(loss+κ*(∑i,w i))=Z^(m+4*ρ+loss+κ*(∑i,w i)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ0.le,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    congr 1
    norm_num
    ring
  calc
    _ = (C*Fc^4*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*bΦ^4*
      ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*
      (1+|t|+T)^J)*(Z^m*(Z^ρ)^4*Z^(loss+κ*(∑i,w i))) := by ring
    _ = _ := by rw [hzpow]

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
