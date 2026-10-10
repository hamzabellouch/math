import OAI.NumberTheory.DirichletL.Moments.FirstMixedExceptionalLow

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedExceptionalDeclared
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstMixedExceptionalCap CenteredMomentFirstMixedCommonRadius

open CenteredMomentFirstMixedExceptionalLow

theorem actual_main_exceptional_declared (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0<K)(hX:0<X)
    (Mdecl : ℝ) (hactual : Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ) ≤ Mdecl)
    (hLow : Real.logb Z X ≤ 5*Mdecl/6) :
    (K*(η.modulus.absNorm:ℝ))*(((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3))≤
      Z^(Mdecl+4*sigma/3+5*(delta+reserve)/6) := by
  have hh:=actual_main_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod hK hX
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:0<(η.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hpow:K*(η.modulus.absNorm:ℝ)=Z^(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)):=by
    rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hn]
  apply (mul_le_mul_of_nonneg_left hh (mul_pos hK hn).le).trans
  rw [hpow,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

theorem actual_error_exceptional_declared (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0<K)(hX:0<X)
    (Mdecl : ℝ) (hactual : Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ) ≤ Mdecl)
    (hLow : Real.logb Z X ≤ 5*Mdecl/6) :
    (K*(η.modulus.absNorm:ℝ))*(((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3))≤
      Z^(Mdecl+3*sigma/2+5*(delta+reserve)/6) := by
  have hh:=actual_error_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod M H Sbad hbad p0 hp0 k hk hK hX
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:0<(η.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hpow:K*(η.modulus.absNorm:ℝ)=Z^(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)):=by
    rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hn]
  apply (mul_le_mul_of_nonneg_left hh (mul_pos hK hn).le).trans
  rw [hpow,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

end SevenEighths.CenteredMomentFirstMixedExceptionalDeclared

end

end OAI
