import OAI.NumberTheory.DirichletL.Moments.FirstMixedExceptionalCap

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedDiagonal
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedExceptionalCap
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstExceptionalPrefactor CenteredMomentDescentLedger
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCanonicalFirst CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O

theorem actual_common_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z w wo branch sigma delta reserve eps:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)
    (hw:0≤w)(hwo:0≤wo)(heps:0≤eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=nominalLog C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    (V/(C.absNorm:ℝ))*Z^(-wo)*
      Z^(K0+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve)*
      (V/(C.absNorm:ℝ)/Z^w)^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        branch*sigma+delta+reserve+eps*Real.logb Z V):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hnc:=norm_pos C hC.1
  have hnd:=norm_pos D hD.1
  have hne:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hnr:=active_norm_pos C D
  have hnq:=norm_pos _ τ.modulus_ne_bot
  have hη:=norm_pos _ η.modulus_ne_bot
  have hf:=fixedPresentationCost_pos
  have hc:0≤Real.logb Z (C.absNorm:ℝ):=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1))
  have hd:0≤Real.logb Z (D.absNorm:ℝ):=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1))
  have hallow:=allowance_nonneg C D Z
  have hfix:=fixed_presentation_log_nonneg Z hZ
  have hm:max (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)-2*w+wo) 0≤
      Real.logb Z (D.absNorm:ℝ)+wo:=max_le (by linarith) (by linarith)
  have he:eps*(Real.logb Z (C.absNorm:ℝ)+w)≥0:=mul_nonneg heps (add_nonneg hc hw)
  have hq:=actual_reference_width η τ C D hC E K Z hK hZ hmod
  have hnom:nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z=
      Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)+2*Real.logb Z V-
      Real.logb Z K-Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ):=by
    rw [nominalLog,nominal_equal_support C D _ hC.1 hD.1 hCD K V]
    simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow]
    ring
  dsimp only
  apply (Real.logb_le_iff_le_rpow hZ (by positivity)).mp
  simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_rpow hz hZ.ne',Real.logb_rpow_eq_mul_logb_of_pos,Real.logb_pow]
  rw [hnom]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hq,hm,he,hfix,hallow]

theorem actual_main_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve eps:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)(heps:0≤eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    (V/(C.absNorm:ℝ))*mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve*(V/(C.absNorm:ℝ))^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        2*sigma+delta+reserve+eps*Real.logb Z V):=by
  simpa only [mainCommonRadius,zero_mul,mul_zero,sub_zero,add_zero,neg_zero,
    Real.rpow_zero,mul_one,div_one] using
    actual_common_diagonal η τ C D hC hD hCD E K V Z 0 0 2 sigma delta reserve eps
      hK hV hZ (le_refl _) (le_refl _) heps hmod

theorem actual_error_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve eps:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)(heps:0≤eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    (V/(C.absNorm:ℝ))*localErrorCost p (k-1)*errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k*(V/(C.absNorm:ℝ)/(normValue p)^k)^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        sigma+delta+reserve+eps*Real.logb Z V):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hpv:=normValue_pos p hp
  have hcpos:=norm_pos C hC.1
  have hqpos:=norm_pos _ τ.modulus_ne_bot
  have hl:0≤Real.logb Z (normValue p):=Real.logb_nonneg hZ (normValue_ge_one p hp)
  have hw:0≤errorRemoval p Z k:=by unfold errorRemoval;positivity
  have hwo:0≤errorMoving p Z k:=by unfold errorMoving;split_ifs <;> positivity
  have hh:=actual_common_diagonal η τ C D hC hD hCD E K V Z
    (errorRemoval p Z k) (errorMoving p Z k) 1 sigma delta reserve eps hK hV hZ hw hwo heps hmod
  dsimp only at hh
  rw [one_mul,errorRemoval_power p hp Z hZ k] at hh
  apply le_trans ?_ hh
  unfold errorCommonRadius
  gcongr
  exact actual_error_weight p hp Z hZ k hk

end SevenEighths.CenteredMomentFirstMixedDiagonal

end

end OAI
