import OAI.NumberTheory.DirichletL.Moments.AmplifiedChildWidth
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedActiveCapacitySource
import OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacityCommon

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyAmplifiedChildWidth
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAmplifiedActiveCapacitySource CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstAnnularInput CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondDyadicRowSupport CenteredMomentSecondRadicalBudget
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstScale CenteredMomentAmplifiedChildWidth
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι]
local instance {α:Type*}:DecidableEq α:=Classical.decEq _

lemma ball_support : Function.support (ballProfile:ℝ→ℂ)⊆Set.Iic (2:ℝ) := by
  intro x hx
  by_cases h:0≤x
  · exact (ballProfile_support_upper x h hx).le
  · exact (lt_of_not_ge h).le.trans (by norm_num)

theorem actual_ball_witness (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z:O,z≠0 ∧ ballProfile (normValue z/dyadicScale (n 1))=1 := by
  obtain ⟨z,_,hz,hz0,_⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U R rows W K n hne
  refine ⟨z,hz0,ballProfile_one _ (div_nonneg (normValue_pos z hz0).le (dyadicScale_pos _).le) ?_⟩
  exact (div_le_one (dyadicScale_pos _)).mpr (dyadicRows_norm rows n z hz).2.le

def geometry (N:ℕ)(b:ℝ):ℝ := (b^N)^2

lemma geometry_pos (N:ℕ)(b:ℝ)(hb:1≤b):0<geometry N b := by
  unfold geometry
  exact sq_pos_of_pos (pow_pos (zero_lt_one.trans_le hb) _)

lemma main_nominal_cap (N:ℕ)(b:ℝ)(hb:1≤b)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t K:ℝ)(hK:0<K)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    nominal (child s C R B τ t) K≤geometry N b*((volume s/(C.absNorm:ℝ))^2/K) := by
  have hv:=common_volume_le N b hb s hc hs C R B τ t hne
  have hC:=CenteredMomentAmplificationChildSourceCaps.norm_ge_one C (allocation_ne s C B)
  have hh:0≤volume s/(C.absNorm:ℝ):=div_nonneg (volume_pos s).le (by positivity)
  have hv':volume (child s C R B τ t)≤b^N*(volume s/(C.absNorm:ℝ)):=by simpa only [mul_div_assoc] using hv
  have hp:volume (child s C R B τ t)^2≤(b^N)^2*(volume s/(C.absNorm:ℝ))^2:=by
    nlinarith [volume_pos (child s C R B τ t),mul_nonneg (pow_nonneg (zero_le_one.trans hb) N) hh]
  exact (div_le_div_of_nonneg_right hp hK.le).trans_eq (by unfold geometry;ring)

lemma error_volume_cap (N:ℕ)(b:ℝ)(hb:1≤b)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (hslot:∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))(υ:Character)(v:ℝ) :
    volume (errorInput s C R B τ t Q k Bp υ v)≤
      b^N*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
  have hv:=common_volume_le N b hb s hc hs C R B τ t hne
  have hq:0≤(Q.absNorm:ℝ)^k:=pow_nonneg (Nat.cast_nonneg _) _
  have hh:=div_le_div_of_nonneg_right hv hq
  rw [common_volume] at hh
  rw [active_error_volume s C R B τ t Q hQ k hslot Bp υ v]
  convert hh using 1 <;> ring

lemma error_nominal_cap (N:ℕ)(b:ℝ)(hb:1≤b)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (hslot:∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ:Character)(v K:ℝ)(hK:0<K) :
    nominal (errorInput s C R B τ t Q k Bp υ v) K≤
      geometry N b*((volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k))^2/K) := by
  have hv:=error_volume_cap N b hb s hc hs C R B τ t hne Q hQ k hslot Bp υ v
  have hh:0≤volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k):=
    div_nonneg (volume_pos s).le (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
  have hp:volume (errorInput s C R B τ t Q k Bp υ v)^2≤
      (b^N)^2*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k))^2:=by
    nlinarith [volume_pos (errorInput s C R B τ t Q k Bp υ v),
      mul_nonneg (pow_nonneg (zero_le_one.trans hb) N) hh]
  exact (div_le_div_of_nonneg_right hp hK.le).trans_eq (by unfold geometry;ring)

lemma restored_nominal_eq (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (hslot:∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ:Character)(v K:ℝ) :
    nominal (restoredError s C R B τ t Q k Bp υ v) K=
      nominal (errorInput s C R B τ t Q k Bp υ v) K := by
  unfold nominal
  rw [restoredError_volume s C R B τ t Q hQ k hslot Bp υ v,
    active_error_volume s C R B τ t Q hQ k hslot Bp υ v]

def mainRadius (C D:Ideal O)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ):ℝ :=
  mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V))
    (Real.logb Z (C.absNorm:ℝ)) σ δ reserve

def errorRadius (C D:Ideal O)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ)(p:O)(k:ℕ):ℝ :=
  errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V))
    (Real.logb Z (C.absNorm:ℝ)) σ δ reserve p k

lemma mainRadius_eq (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ):
    mainRadius C D E K V Z σ δ reserve=
      mainCommonRadius Z (Real.logb Z ((commonPart D C).absNorm:ℝ))
        (nominalLog C D (∏P∈E,P.val) K V Z)
        (Real.logb Z ((commonPart C D).absNorm:ℝ)) σ δ reserve := by
  rw [commonPart_eq_left C D hC.1 hCD,commonPart_eq_left D C hD.1 hCD.symm]
  simp only [mainRadius,nominalLog,primeSubsetGenerator,span_idealGenerator]

lemma errorRadius_eq (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ)(p:O)(k:ℕ):
    errorRadius C D E K V Z σ δ reserve p k=
      errorCommonRadius Z (Real.logb Z ((commonPart D C).absNorm:ℝ))
        (nominalLog C D (∏P∈E,P.val) K V Z)
        (Real.logb Z ((commonPart C D).absNorm:ℝ)) σ δ reserve p k := by
  rw [commonPart_eq_left C D hC.1 hCD,commonPart_eq_left D C hD.1 hCD.symm]
  simp only [errorRadius,nominalLog,primeSubsetGenerator,span_idealGenerator]

def threshold (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ):ℝ :=
  fixedWidthThreshold 2 (geometry N b) σ (by norm_num) (geometry_pos N b hb) hσ

lemma threshold_gt_one (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ):1<threshold N b σ hb hσ :=
  (fixedWidthThreshold_spec 2 (geometry N b) σ (by norm_num) (geometry_pos N b hb) hσ).1

theorem main_child_width (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ)
    (Z:ℝ)(hlarge:threshold N b σ hb hσ≤Z)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C D R:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(τ:Character)(t:ℝ)
    (hB:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (K δ reserve ξ q Mparent:ℝ)(hK:0<K)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hη:(s.η.modulus.absNorm:ℝ)≤Z^q)(hparent:Real.logb Z K+q≤Mparent)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)(hC₂:Supported C₂)(hD₂:Supported D₂)
    (U:Finset (CommonIndex C₂ D₂))(family:RayCharacter→Character)
    (hf:Family τ C₂ D₂ hC₂ hD₂ U family)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hne:physicalBlock τ t S β C₂ D₂ hC₂ hD₂ U
      (frequencyRadius (nominal (child s C R B τ t) (mainRadius C D E K (volume s) Z σ δ reserve)) Z ξ)
      rows W (mainRadius C D E K (volume s) Z σ δ reserve) n≠0)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)<Mparent-σ/2 := by
  have hZ:1<Z:=(threshold_gt_one N b σ hb hσ).trans_le hlarge
  let L:=mainRadius C D E K (volume s) Z σ δ reserve
  have hL:0<L:=by unfold L mainRadius mainCommonRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have he:=mainRadius_eq C D hC hD hCD E K (volume s) Z σ δ reserve
  have hscale:=main_nominal_cap N b hb s hc hs C R B τ t L hL hB
  have hhscale:nominal (child s C R B τ t) L≤geometry N b*
      ((volume s/((commonPart C D).absNorm:ℝ))^2/L):=by
    simpa only [commonPart_eq_left C D hC.1 hCD] using hscale
  obtain ⟨z,hz,hball⟩:=actual_ball_witness τ t S β C₂ D₂ hC₂ hD₂ U _ rows W L n hne
  have hw:=main_declared_width_drop s.η τ fixedBadMask fixedBadMask_ne_zero C D E
    K (volume s) Z σ δ reserve hK (volume_pos s) hZ hmod hf t S β rows W
    (nominal (child s C R B τ t) L) (geometry N b) ξ (nominal_pos _ L hL)
    (geometry_pos N b hb) (by simpa only [←he] using hhscale) n
    (by simpa only [←he] using hne) χ ballProfile 2 (by norm_num) ball_support z hz
    (by rw [hball];exact one_ne_zero) rfl q hη hσ hδ hr hξ hlarge
  have hlog:Real.logb Z (dyadicScale (n 1))≤Real.logb Z (max 1 (2*dyadicScale (n 1))):=by
    apply Real.logb_le_logb_of_le hZ (dyadicScale_pos _)
    exact (by linarith [dyadicScale_pos (n 1)]:dyadicScale (n 1)≤2*dyadicScale (n 1)).trans (le_max_right _ _)
  linarith

theorem error_child_width (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ)
    (Z:ℝ)(hlarge:threshold N b σ hb hσ≤Z)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C D R:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(τ:Character)(t:ℝ)
    (hB:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=0∨k=5∨k=6)
    (hslot:∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^(k+1)))
    (υ:Character)(χ₀:RayCharacter)(v:ℝ)
    (hN:υ.modulus.absNorm≤radicalBound (childCharacter τ χ₀) fixedBadMask p (errorMovingExponent k))
    (K δ reserve ξ q Mparent:ℝ)(hK:0<K)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hη:(s.η.modulus.absNorm:ℝ)≤Z^q)(hparent:Real.logb Z K+q≤Mparent)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)(hC₂:Supported C₂)(hD₂:Supported D₂)
    (U:Finset (CommonIndex C₂ D₂))(family:RayCharacter→Character)
    (hf:Family υ C₂ D₂ hC₂ hD₂ U family)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U
      (frequencyRadius (nominal (errorInput s C R B τ t (Ideal.span {p}) (k+1) Bp υ v)
        (errorRadius C D E K (volume s) Z σ δ reserve p (k+1))) Z ξ)
      rows W (errorRadius C D E K (volume s) Z σ δ reserve p (k+1)) n≠0)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)<Mparent-σ/2 := by
  have hZ:1<Z:=(threshold_gt_one N b σ hb hσ).trans_le hlarge
  have hQ:Ideal.span {p}≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  let L:=errorRadius C D E K (volume s) Z σ δ reserve p (k+1)
  have hL:0<L:=by unfold L errorRadius errorCommonRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have he:=errorRadius_eq C D hC hD hCD E K (volume s) Z σ δ reserve p (k+1)
  have hscale:=error_nominal_cap N b hb s hc hs C R B τ t hB (Ideal.span {p}) hQ (k+1) hslot Bp υ v L hL
  have hpn:((Ideal.span {p}).absNorm:ℝ)=normValue p:=rfl
  have hhscale:nominal (errorInput s C R B τ t (Ideal.span {p}) (k+1) Bp υ v) L≤geometry N b*
      ((volume s/((commonPart C D).absNorm*(normValue p)^(k+1)))^2/L):=by
    simpa only [commonPart_eq_left C D hC.1 hCD,hpn] using hscale
  obtain ⟨z,hz,hball⟩:=actual_ball_witness υ v S β C₂ D₂ hC₂ hD₂ U _ rows W L n hne
  have hw:=error_declared_width_drop s.η τ fixedBadMask fixedBadMask_ne_zero C D E
    K (volume s) Z σ δ reserve hK (volume_pos s) hZ hmod υ χ₀ p hp k hk hN hf v S β rows W
    (nominal (errorInput s C R B τ t (Ideal.span {p}) (k+1) Bp υ v) L) (geometry N b) ξ
    (nominal_pos _ L hL) (geometry_pos N b hb) (by simpa only [←he] using hhscale) n
    (by simpa only [←he] using hne) χ ballProfile 2 (by norm_num) ball_support z hz
    (by rw [hball];exact one_ne_zero) rfl q hη hσ hδ hr hξ hlarge
  have hlog:Real.logb Z (dyadicScale (n 1))≤Real.logb Z (max 1 (2*dyadicScale (n 1))):=by
    apply Real.logb_le_logb_of_le hZ (dyadicScale_pos _)
    exact (by linarith [dyadicScale_pos (n 1)]:dyadicScale (n 1)≤2*dyadicScale (n 1)).trans (le_max_right _ _)
  linarith

end SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

end

end OAI
