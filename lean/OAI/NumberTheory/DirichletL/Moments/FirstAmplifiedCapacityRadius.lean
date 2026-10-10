import OAI.NumberTheory.DirichletL.Moments.FirstMixedNormalizationActual
import OAI.NumberTheory.DirichletL.Moments.FirstMixedCommonRadius

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedCapacityRadius
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstPhysicalSource
open CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentFirstCanonicalFamily CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentFirstScale ConcreteTraceCRT
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadiusSaving
local notation "O"=>HeckeFamily.O

lemma enlarged_gain_extraction (c d w wo sigma branch delta reserve:ℝ)
    (_hw:0≤w)(hwo:wo≤2*w):
    -d+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve≤
      -min c d+branch*sigma+delta+reserve := by
  have h:max (d-c-2*w+wo) 0≤d-min c d:=by
    apply max_le <;> linarith [min_le_left c d,min_le_right c d]
  linarith

theorem actual_reference_shift (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z red w wo cost gain:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hred:0<red)(hcost:0<cost)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    Real.logb Z (Z^(K0+gain))-
      Real.logb Z (cost*(τ.modulus.absNorm:ℝ)*Z^wo)-Real.logb Z (V/(red*Z^w))=
      Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        Real.logb Z red-c-d+gain+w-wo-
        Real.logb Z fixedPresentationCost-Real.logb Z cost := by
  have hc:=norm_pos C hC.1
  have hd:=norm_pos D hD.1
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hE:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR:=active_norm_pos C D
  have hz:0<Z:=zero_lt_one.trans hZ
  have hh:=actual_reference_width η τ C D hC E K Z hK hZ hmod
  dsimp only
  rw [nominal_equal_support C D _ hC.1 hD.1 hCD K V]
  simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow,
    Real.logb_rpow hz hZ.ne'] at hh ⊢
  norm_num at hh ⊢
  linarith

theorem actual_main_reference_shift (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z red sigma delta reserve:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hred:0<red)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-
      Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z (V/red)≤
      Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        (Real.logb Z red-c)-min c d+2*sigma+delta+reserve-
        Real.logb Z fixedPresentationCost := by
  have hh:=actual_reference_shift η τ C D hC hD hCD E K V Z red 0 0 1
    (max (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)) 0+2*sigma+delta+reserve)
    hK hV hZ hred (by norm_num) hmod
  have hg:=enlarged_gain_extraction (Real.logb Z (C.absNorm:ℝ))
    (Real.logb Z (D.absNorm:ℝ)) 0 0 sigma 2 delta reserve (by norm_num) (by norm_num)
  dsimp only at hh ⊢
  simp only [Real.rpow_zero,mul_one,one_mul,Real.logb_one,add_zero,sub_zero] at hh hg
  change _≤_
  rw [mainCommonRadius]
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh ⊢
  norm_num at hg
  linarith

theorem actual_error_reference_shift (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z red sigma delta reserve cost:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hred:0<red)(hcost:0<cost)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (p:O)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤sigma)
    (hl:sigma/6≤Real.logb Z (normValue p)):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-
      Real.logb Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))-
      Real.logb Z (V/(red*Z^(errorRemoval p Z k)))≤
      Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        (Real.logb Z red-c)-min c d+6*errorRemoval p Z k+delta+reserve-
        Real.logb Z fixedPresentationCost-Real.logb Z cost := by
  have hp:0≤Real.logb Z (normValue p):=by linarith
  have hw:0≤errorRemoval p Z k:=by unfold errorRemoval;positivity
  have hwo:errorMoving p Z k≤2*errorRemoval p Z k:=by
    rcases hk with rfl|rfl|rfl <;> simp only [errorMoving,errorRemoval] <;> norm_num <;> linarith
  have he:sigma+errorRemoval p Z k-errorMoving p Z k≤6*errorRemoval p Z k:=by
    rcases hk with rfl|rfl|rfl <;> simp only [errorMoving,errorRemoval] <;> norm_num <;> linarith
  have hh:=actual_reference_shift η τ C D hC hD hCD E K V Z red
    (errorRemoval p Z k) (errorMoving p Z k) cost
    (max (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)-
      2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+delta+reserve)
    hK hV hZ hred hcost hmod
  have hg:=enlarged_gain_extraction (Real.logb Z (C.absNorm:ℝ))
    (Real.logb Z (D.absNorm:ℝ)) (errorRemoval p Z k) (errorMoving p Z k)
    sigma 1 delta reserve hw hwo
  dsimp only at hh ⊢
  simp only [one_mul] at hg
  rw [errorCommonRadius]
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh ⊢
  linarith

end SevenEighths.CenteredMomentFirstAmplifiedCapacityRadius

end

end OAI
