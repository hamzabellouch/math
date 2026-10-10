import OAI.NumberTheory.DirichletL.Energy.State
import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalChosenBlock
import OAI.NumberTheory.DirichletL.Moments.SecondChildRadialWidth
import OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyChildState
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentEnergyState CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondDyadicRowSupport CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O

lemma ball_support : Function.support (ballProfile:ℝ→ℂ)⊆Set.Iic (2:ℝ):=by
  intro x hx
  by_cases h:0≤x
  · exact (CenteredMomentAmplifiedRetainedRadius.ballProfile_support_upper x h hx).le
  · exact (lt_of_not_ge h).le.trans (by norm_num)

lemma canonical_mask_nonexceptional (τ:Character)(Q R:Ideal O)(hR:R≠0)
    (n:Fin 4→ℤ)(z:O)(hz:(canonicalRadial τ Q n).keep z):
    ¬CenteredExceptionalProfile.FixedInducingRow τ Q
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z:=by
  intro hh
  exact hz.2 ((CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff τ Q
    fixedBadMask (ConcretePrimeRowBridge.idealGenerator R) 1 z fixedBadMask_ne_zero
    (ConcretePrimeRowBridge.idealGenerator_ne_zero R hR) one_ne_zero hz.1
    (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hh)

def canonicalState (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)
    (hn:1≤dyadicScale (n 1)):NaturalState Z Bmask 2 where
  character:=τ
  fixedModulus:=Q
  puncture:=R
  radial:=canonicalRadial τ Q n
  rowWidth:=Real.logb Z (dyadicScale (n 1))
  characterWidth:=Real.logb Z (τ.modulus.absNorm:ℝ)
  base_ge_one:=hZ.le
  row_nonneg:=Real.logb_nonneg hZ hn
  character_nonneg:=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))
  scale_eq:=(Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _)).symm
  modulus_bound:=by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  puncture_ne_zero:=hR
  puncture_bound:=hRN
  radial_support:=ball_support
  row_ne_zero:=fun _ hz=>hz.1
  nonexceptional:=canonical_mask_nonexceptional τ Q R hR n

lemma canonicalState_width (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)(hn:1≤dyadicScale (n 1)):
    (canonicalState Z Bmask hZ τ Q R hR hRN n hn).width=
      Real.logb Z (dyadicScale (n 1))+Real.logb Z (τ.modulus.absNorm:ℝ):=rfl

lemma canonicalState_power (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)(hn:1≤dyadicScale (n 1)):
    Z^(canonicalState Z Bmask hZ τ Q R hR hRN n hn).width=
      (τ.modulus.absNorm:ℝ)*dyadicScale (n 1):=by
  rw [canonicalState_width,Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  ring

lemma common_puncture_bound (Z Bmask Bsource:ℝ)(hZ:0<Z)(R C:Ideal O)
    (hR:(R.absNorm:ℝ)≤Z^Bmask)(hC:(C.absNorm:ℝ)≤Z^Bsource):
    ((R*C).absNorm:ℝ)≤Z^(Bmask+Bsource):=by
  rw [map_mul,Nat.cast_mul,Real.rpow_add hZ]
  exact mul_le_mul hR hC (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)

section Actual
variable {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
  {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
  (h:Family η C D hC hD U τ)
  (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
  (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
  (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)

include hne in

lemma actual_dyad_ge_one : 1≤dyadicScale (n 1):=by
  obtain ⟨z,_,hz,hz0,_⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U
    radius rows W K n hne
  exact (normValue_ge_one z hz0).trans (dyadicRows_norm rows n z hz).2.le

def actualState (Z Bmask:ℝ)(hZ:1<Z)(χ:RayCharacter)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask):NaturalState Z Bmask 2:=
  canonicalState Z Bmask hZ (τ χ) Q R hR hRN n
    (actual_dyad_ge_one t S β radius rows W K n hne)

include h hK in

theorem actualState_width (Z Bmask:ℝ)(hZ:1<Z)(χ:RayCharacter)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask):
    (actualState (τ:=τ) t S β radius rows W K n hne Z Bmask hZ χ Q R hR hRN).width≤
      Real.logb Z radius+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)):=by
  exact dyadic_log_budget h t S β radius rows W K hK n hne Z hZ χ

end Actual
end SevenEighths.CenteredMomentEnergyChildState

end

end OAI
