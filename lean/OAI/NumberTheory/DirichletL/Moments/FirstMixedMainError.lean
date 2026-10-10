import OAI.NumberTheory.DirichletL.Moments.FirstMixedNormalizationActual
import OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedMainError
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstMixedNormalization CenteredMomentFirstSourceConductorCaps
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem actual_error_conductor_weight (ρ υ:Character)(χ:RayFourExpansion.RayCharacter)
    (p:O)(hp:p≠0)(n:ℕ)(hn:n=0 ∨ n=5 ∨ n=6)(Z:ℝ)(hZ:1<Z)
    (hυ:υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p (errorMovingExponent n)):
    localErrorCost p n*(υ.modulus.absNorm:ℝ)≤rayCost*(ρ.modulus.absNorm:ℝ):=by
  have hray:=CenteredMomentSecondRadicalBudget.child_modulus_bound ρ χ
  have hN:(υ.modulus.absNorm:ℝ)≤
      ((childCharacter ρ χ).modulus.absNorm:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*Z^(errorMoving p Z (n+1)):=by
    rw [←radicalBound_error_power (childCharacter ρ χ) fixedBadMask p hp Z hZ n hn]
    exact_mod_cast hυ
  have hcap:(υ.modulus.absNorm:ℝ)≤
      rayCost*(ρ.modulus.absNorm:ℝ)*Z^(errorMoving p Z (n+1)):=by
    apply hN.trans
    have hr:((childCharacter ρ χ).modulus.absNorm:ℝ)≤
        (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm:=by exact_mod_cast hray
    calc
      _≤((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          Z^(errorMoving p Z (n+1)):=by gcongr
      _=_:=by unfold rayCost fixedPresentationCost;ring
  have hk:n+1=1 ∨ n+1=6 ∨ n+1=7:=by omega
  have hc:=actual_error_weight p hp Z hZ (n+1) hk
  simp only [Nat.add_sub_cancel] at hc
  have hh:=mul_le_mul hc hcap (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  apply hh.trans_eq
  calc
    _=(rayCost*(ρ.modulus.absNorm:ℝ))*(Z^(-errorMoving p Z (n+1))*Z^(errorMoving p Z (n+1))):=by ring
    _=_:=by rw [←Real.rpow_add (zero_lt_one.trans hZ),neg_add_cancel,Real.rpow_zero,mul_one]

theorem actual_main_error_reference (ρ υ:Character)(χ:RayFourExpansion.RayCharacter)
    (p:O)(hp:p≠0)(n:ℕ)(hn:n=0 ∨ n=5 ∨ n=6)(Z V C B E:ℝ)
    (hZ:1<Z)(hV:0<V)(hC:0<C)(hE:0≤E)
    (hυ:υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p (errorMovingExponent n)):
    (V/C)*localErrorCost p n*(υ.modulus.absNorm:ℝ)*(V/C/(normValue p)^(n+1))*E/
      ((ρ.modulus.absNorm:ℝ)*(V/C)^2*Z^B)≤
      rayCost*Z^(-errorRemoval p Z (n+1)-B)*E:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hpv:=normValue_pos p hp
  have hq:0<(ρ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ρ.modulus_ne_bot)
  have hh:=actual_error_conductor_weight ρ υ χ p hp n hn Z hZ hυ
  calc
    _=((V/C)*(localErrorCost p n*(υ.modulus.absNorm:ℝ))*(V/C/(normValue p)^(n+1))*E)/
        ((ρ.modulus.absNorm:ℝ)*(V/C)^2*Z^B):=by ring
    _≤((V/C)*(rayCost*(ρ.modulus.absNorm:ℝ))*(V/C/(normValue p)^(n+1))*E)/
        ((ρ.modulus.absNorm:ℝ)*(V/C)^2*Z^B):=by gcongr
    _=rayCost*Z^(-errorRemoval p Z (n+1)-B)*E:=by
      rw [Real.rpow_sub hz,Real.rpow_neg hz.le,errorRemoval_power p hp Z hZ (n+1)]
      field_simp

end SevenEighths.CenteredMomentFirstMixedMainError

end

end OAI
