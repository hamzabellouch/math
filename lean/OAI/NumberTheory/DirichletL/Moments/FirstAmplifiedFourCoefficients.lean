import OAI.NumberTheory.DirichletL.Moments.SecondChildPowerBudget
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPowerBudget
import OAI.NumberTheory.DirichletL.Moments.FirstCommonReferencePower
import OAI.NumberTheory.DirichletL.Moments.FirstMixedExceptionalDeclared
import OAI.NumberTheory.DirichletL.Moments.FirstMixedDiagonal
import OAI.NumberTheory.DirichletL.Moments.SuccessorPaidParameters

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedAllowance
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstMixedExceptionalLow CenteredMomentFirstMixedDiagonal
open CenteredMomentSuccessorPaidParameters
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

def reference (q V C Z allowance:ℝ):ℝ:=q*(V/C)^2*Z^allowance

def mainCores (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ):Fin 4→ℝ:=
  ![(V/C)*q*(V/C)*Z^(ell+deficit/6+paid)/reference q V C Z allowance,
    (V/C)*(V/C)^((1:ℝ)/3)*Kmain^((5:ℝ)/6)*Z^(-2*max r 0/3)/reference q V C Z allowance,
    (V/C)*Kmain*(V/C)^eps/reference q V C Z allowance,
    (V/C)*Kmain*Z^(-saving)/reference q V C Z allowance]

def errorCores (p:O)(k:ℕ)(q V C Z allowance Kerror deficit paid eps saving r:ℝ):Fin 4→ℝ:=
  ![(V/C)*localErrorCost p (k-1)*q*Z^(errorMoving p Z k)*
      (V/C/(normValue p)^k)*Z^(errorRemoval p Z k+deficit/6+paid)/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*(V/C/(normValue p)^k)^((1:ℝ)/3)*
      Kerror^((5:ℝ)/6)*Z^(-2*max r 0/3)/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*Kerror*(V/C/(normValue p)^k)^eps/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*Kerror*Z^(-saving)/reference q V C Z allowance]

def lossVector (sigma delta reserve paid eps Mcap saving:ℝ):Fin 4→ℝ:=
  ![paid,3*sigma/2+5*(delta+reserve)/6,
    2*sigma+delta+reserve+eps*Mcap,2*sigma+delta+reserve-saving]

def averagedCoefficients (P:Finset (Ideal O))(mainFactor:ℝ)(H main:Fin 4→ℝ)
    (error:elementPool P→Fin 3→Ray→Fin 4→ℝ):Fin 4→ℝ:=fun j=>
  (56/(P.card:ℝ))*(mainFactor*H j*main j+
    ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)

lemma actual_valuation_mass : (∑i:Fin 3,16*(errorIndex i+2:ℝ)^2)=1872 := by
  norm_num [Fin.sum_univ_succ,errorIndex]

theorem actual_error_average (P:Finset (Ideal O))(hne:P.Nonempty)
    (hp:∀Q∈P,Prime Q)(hbad:∀Q∈P,Q∉fixedBadPrimes)
    (f:elementPool P→Fin 3→Ray→ℝ)(E:ℝ)(_hE:0≤E)
    (hf:∀p i χ,f p i χ≤E):
    (1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
      16*(errorIndex i+2:ℝ)^2*∑χ:Ray,f p i χ)≤
        1872*(Fintype.card Ray:ℝ)*E := by
  have hn:(0:ℝ)<P.card:=by exact_mod_cast hne.card_pos
  have hc:Fintype.card (elementPool P)=P.card:=by
    rw [Fintype.card_coe,elementPool_card P hp hbad]
  have hh:(∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,f p i χ)≤
      ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,E:=by
    apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _=>hf p i χ)) (by positivity)
  apply (mul_le_mul_of_nonneg_left hh (by positivity:0≤1/(P.card:ℝ))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←Finset.sum_mul,actual_valuation_mass,hc]
  field_simp

lemma main_paid_core (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ)
    (hq:0<q)(hV:0<V)(hC:0<C)(hZ:1<Z)(hB:0≤allowance)(hdef:0≤deficit):
    Z^(-ell)*mainCores q V C Z allowance Kmain ell deficit paid eps saving r 0≤
      Z^(deficit+paid) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hx:0<V/C:=div_pos hV hC
  have he:mainCores q V C Z allowance Kmain ell deficit paid eps saving r 0=
      Z^(ell+deficit/6+paid-allowance):=by
    dsimp [mainCores,reference]
    rw [Real.rpow_sub hz]
    field_simp
  rw [he,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

lemma error_paid_core (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)
    (q V C Z allowance Kerror deficit paid eps saving r:ℝ)
    (hq:0<q)(hV:0<V)(hC:0<C)(hZ:1<Z)(hB:0≤allowance)(hdef:0≤deficit):
    errorCores p k q V C Z allowance Kerror deficit paid eps saving r 0≤Z^(deficit+paid) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hx:0<V/C:=div_pos hV hC
  have hpv:=normValue_pos p hp
  have hw:=actual_error_weight p hp Z hZ k hk
  have hs:localErrorCost p (k-1)*Z^(errorMoving p Z k)≤1:=by
    have hh:=mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hz.le (errorMoving p Z k))
    rw [←Real.rpow_add hz,neg_add_cancel,Real.rpow_zero] at hh
    exact hh
  have he:errorCores p k q V C Z allowance Kerror deficit paid eps saving r 0=
      (localErrorCost p (k-1)*Z^(errorMoving p Z k))*Z^(deficit/6+paid-allowance):=by
    dsimp [errorCores,reference]
    rw [Real.rpow_sub hz,show errorRemoval p Z k+deficit/6+paid=
      errorRemoval p Z k+(deficit/6+paid) by ring,Real.rpow_add hz,errorRemoval_power p hp Z hZ k]
    field_simp
  rw [he]
  calc
    _≤1*Z^(deficit/6+paid-allowance):=mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hz.le _)
    _≤Z^(deficit+paid):=by rw [one_mul];apply Real.rpow_le_rpow_of_exponent_le hZ.le;linarith

theorem actual_main_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving r Mdecl Mcap:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0≤sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    ∀j:Fin 4,Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kmain (sigma/3) (Mdecl-M0) paid eps saving r j≤
      Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hr:0<mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  have havg:Z^(-sigma/3)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hZ.le (by linarith)
  have hA:Real.logb Z V≤Mdecl:=by linarith
  have hAcap:Real.logb Z V≤Mcap:=hA.trans hcap
  intro j
  fin_cases j
  · have hh:=main_paid_core (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector,neg_div] using hh
  · have hh:=actual_main_exceptional_reference η τ C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve r hZ hmod hK hV
    have ht:Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 1≤
        Z^(Real.logb Z V-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+
          4*sigma/3+5*(delta+reserve)/6):=by
      convert hh using 1 ; dsimp [mainCores,reference] ; ring
    apply ht.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith
  · have hh:=actual_main_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve eps hK hV hZ heps hmod
    have hc0:0≤mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 2:=by
      dsimp [mainCores,reference];positivity
    apply (mul_le_mul_of_nonneg_right havg hc0).trans
    rw [one_mul]
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    have he:=mul_le_mul_of_nonneg_left hAcap heps
    linarith
  · have hh:=actual_main_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve 0 hK hV hZ (by norm_num) hmod
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    have hcore:mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          2*sigma+delta+reserve)*Z^(-saving):=by
      convert ht using 1 ; dsimp [mainCores,reference] ; ring
    have ht':=mul_le_mul_of_nonneg_left hcore (Real.rpow_nonneg hz.le (-sigma/3))
    apply ht'.trans
    calc
      _≤1*(Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          2*sigma+delta+reserve)*Z^(-saving)):=mul_le_mul_of_nonneg_right havg (by positivity)
      _≤_:=by
        rw [one_mul,←Real.rpow_add hz]
        apply Real.rpow_le_rpow_of_exponent_le hZ.le
        dsimp [lossVector]
        linarith

theorem actual_error_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving r Mdecl Mcap:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0≤sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))(hbad:fixedBadPrimes⊆Sbad)
    (p:O)(hp:p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k;
    ∀j:Fin 4,errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kerror (Mdecl-M0) paid eps saving r j≤
      Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hpdata:=elementPool_data _ (fun Q hQ=>(primePool_data M H Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad _ _ _ Q hQ).2) p hp
  have hp0:p≠0:=hpdata.1.ne_zero
  have hr:0<errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by unfold errorCommonRadius;positivity
  have hA:Real.logb Z V≤Mdecl:=by linarith
  have hAcap:Real.logb Z V≤Mcap:=hA.trans hcap
  intro j
  fin_cases j
  · have hh:=error_paid_core p hp0 k hk (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
      (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector] using hh
  · have hh:=actual_error_exceptional_reference η τ C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve r hZ hmod M H Sbad hbad p hp k hk hK hV
    have ht:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 1≤
        Z^(Real.logb Z V-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+
          3*sigma/2+5*(delta+reserve)/6):=by
      convert hh using 1 ; dsimp [errorCores,reference] ; ring
    apply ht.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith
  · have hh:=actual_error_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve eps hK hV hZ heps hmod p hp0 k hk
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    have he:=mul_le_mul_of_nonneg_left hAcap heps
    linarith
  · have hh:=actual_error_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve 0 hK hV hZ (by norm_num) hmod p hp0 k hk
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    have hcore:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          sigma+delta+reserve)*Z^(-saving):=by
      convert ht using 1 ; dsimp [errorCores,reference] ; ring
    apply hcore.trans
    rw [←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith

def sourceCoefficients (P:Finset (Ideal O))(mainFactor:ℝ)(amain:Fin 4→ℝ)
    (aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ):Fin 4→ℝ:=fun j=>
  (56/(P.card:ℝ))*(mainFactor*amain j+
    ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*localErrorCost p (errorIndex i)*
      ∑χ:Ray,aerror p i χ j*((normValue p)^(errorIndex i+1))^(-alpha j))

lemma shortened_power (V q:ℝ)(k:ℕ)(alpha:ℝ)(hV:0≤V)(hq:0≤q):
    (V/q^k)^alpha=V^alpha*(q^k)^(-alpha):=by
  rw [Real.div_rpow hV (pow_nonneg hq k),Real.rpow_neg (pow_nonneg hq k),div_eq_mul_inv]

theorem source_coefficients_identity (P:Finset (Ideal O))(mainFactor V:ℝ)(hV:0≤V)
    (amain:Fin 4→ℝ)(aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ):
    (∑j:Fin 4,sourceCoefficients P mainFactor amain aerror alpha j*V^(alpha j))=
    (56/(P.card:ℝ))*(mainFactor*(∑j:Fin 4,amain j*V^(alpha j))+
      ∑p:elementPool P,∑i:Fin 3,(16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
        (errorIndex i+2:ℝ)*∑χ:Ray,∑j:Fin 4,aerror p i χ j*
          (V/(normValue p)^(errorIndex i+1))^(alpha j)) := by
  have hnorm:∀p:O,0≤normValue p:=by intro p;unfold normValue;positivity
  let f:=fun (j:Fin 4) (p:elementPool P) (i:Fin 3) (χ:Ray)=>
    16*(errorIndex i+2:ℝ)^2*localErrorCost p (errorIndex i)*
      (aerror p i χ j*((normValue p)^(errorIndex i+1))^(-alpha j))*V^(alpha j)
  have hswap:(∑j:Fin 4,∑p:elementPool P,∑i:Fin 3,∑χ:Ray,f j p i χ)=
      ∑p:elementPool P,∑i:Fin 3,∑χ:Ray,∑j:Fin 4,f j p i χ:=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  calc
    _=(56/(P.card:ℝ))*∑j:Fin 4,
        (mainFactor*amain j*V^(alpha j)+
          (∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*localErrorCost p (errorIndex i)*
            ∑χ:Ray,aerror p i χ j*((normValue p)^(errorIndex i+1))^(-alpha j))*V^(alpha j)):=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      unfold sourceCoefficients
      ring
    _=(56/(P.card:ℝ))*(mainFactor*(∑j:Fin 4,amain j*V^(alpha j))+
        ∑j:Fin 4,∑p:elementPool P,∑i:Fin 3,∑χ:Ray,f j p i χ):=by
      congr 1
      rw [Finset.sum_add_distrib]
      congr 1
      · simp only [Finset.mul_sum,mul_assoc]
      · simp only [f,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    _=(56/(P.card:ℝ))*(mainFactor*(∑j:Fin 4,amain j*V^(alpha j))+
        ∑p:elementPool P,∑i:Fin 3,∑χ:Ray,∑j:Fin 4,f j p i χ):=by rw [hswap]
    _=_:=by
      congr 2
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [shortened_power V (normValue p) _ _ hV (hnorm _)]
      dsimp [f]
      ring

theorem averaged_coefficients_bound (P:Finset (Ideal O))(hne:P.Nonempty)
    (hp:∀Q∈P,Prime Q)(hbad:∀Q∈P,Q∉fixedBadPrimes)
    (Z ell primeLoss mainFactor:ℝ)(hZ:1<Z)(hloss:0≤primeLoss)
    (hfactor:0≤mainFactor)(hcard:Z^(ell-primeLoss)≤(P.card:ℝ))
    (H main loss:Fin 4→ℝ)(error:elementPool P→Fin 3→Ray→Fin 4→ℝ)
    (hH:∀j,0≤H j)(hm:∀j,Z^(-ell)*main j≤Z^(loss j))
    (he:∀p i χ j,error p i χ j≤Z^(loss j)):
    ∀j,averagedCoefficients P mainFactor H main error j≤
      56*(mainFactor+1872*(Fintype.card Ray:ℝ))*H j*Z^(loss j+primeLoss) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:(0:ℝ)<P.card:=by exact_mod_cast hne.card_pos
  have hinv:(1/(P.card:ℝ))≤Z^(-ell+primeLoss):=by
    have hh:=one_div_le_one_div_of_le (Real.rpow_pos_of_pos hz _) hcard
    simpa [one_div,←Real.rpow_neg hz.le,neg_sub,sub_eq_add_neg,add_comm] using hh
  intro j
  have hm':main j≤Z^(ell+loss j):=by
    have hh:=mul_le_mul_of_nonneg_left (hm j) (Real.rpow_nonneg hz.le ell)
    rw [←mul_assoc,←Real.rpow_add hz,add_neg_cancel,Real.rpow_zero,one_mul,
      ←Real.rpow_add hz] at hh
    exact hh
  have hmain:(1/(P.card:ℝ))*main j≤Z^(loss j+primeLoss):=by
    calc
      _≤(1/(P.card:ℝ))*Z^(ell+loss j):=mul_le_mul_of_nonneg_left hm' (by positivity)
      _≤Z^(-ell+primeLoss)*Z^(ell+loss j):=mul_le_mul_of_nonneg_right hinv (by positivity)
      _=Z^(loss j+primeLoss):=by rw [←Real.rpow_add hz];congr 1;ring
  have herr:=actual_error_average P hne hp hbad (fun p i χ=>H j*error p i χ j)
    (H j*Z^(loss j)) (mul_nonneg (hH j) (Real.rpow_nonneg hz.le _)) (fun p i χ=>mul_le_mul_of_nonneg_left (he p i χ j) (hH j))
  have hl:Z^(loss j)≤Z^(loss j+primeLoss):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have herr':(1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
      16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)≤
      1872*(Fintype.card Ray:ℝ)*(H j*Z^(loss j+primeLoss)):=
    herr.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl (hH j)) (by positivity))
  calc
    _=56*(mainFactor*H j*((1/(P.card:ℝ))*main j)+
      (1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
        16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)):=by
      unfold averagedCoefficients;ring
    _≤56*(mainFactor*H j*Z^(loss j+primeLoss)+
      1872*(Fintype.card Ray:ℝ)*(H j*Z^(loss j+primeLoss))):=by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hmain (mul_nonneg hfactor (hH j))) herr') (by norm_num)
    _=_:=by ring

theorem actual_low_four_coefficients
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)(rmain:ℝ)
    (rerror:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3)))→Fin 3→Ray→ℝ):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let main:=mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-M0) paid eps saving rmain;
    let error:=fun (p:elementPool P) (i:Fin 3) (χ:Ray)=>
      errorCores p (errorIndex i+1) (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
        (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ))
          sigma delta reserve p (errorIndex i+1)) (Mdecl-M0) paid eps saving (rerror p i χ);
    ∀j,averagedCoefficients P ((Mamp+2*sigma)/(sigma/6)) H main error j≤
      56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
        Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hne:(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).Nonempty:=by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.rpow_pos_of_pos hz (sigma/3-primeLoss)).trans_le hcard
  have hmain:=actual_main_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
    rmain Mdecl Mcap hK hV hZ hs.le heps hM hcap hactual hlow hmod
  have herror:=fun (p:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))))
      (i:Fin 3) (χ:Ray)=>
    actual_error_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
      (rerror p i χ) Mdecl Mcap hK hV hZ hs.le heps hM hcap hactual hlow hmod
      M Hray Sbad hbad p p.property (errorIndex i+1)
      (by fin_cases i <;> norm_num [errorIndex])
  exact averaged_coefficients_bound _ hne
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).2)
    Z (sigma/3) primeLoss ((Mamp+2*sigma)/(sigma/6)) hZ hloss
    (div_nonneg (by linarith) (by positivity)) hcard H _ _ _ hH
    (by simpa only [neg_div] using hmain) herror

theorem source_normalized_identity (P:Finset (Ideal O))(mainFactor b V C q Z allowance eps:ℝ)
    (N:ℕ)(alpha:Fin 4→ℝ)(amain:Fin 4→ℝ)
    (aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)
    (hV:0<V)(hC:0<C)(hq:0<q)(hZ:0<Z):
    ∀j,CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
        (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C^eps*(b^N)^(alpha j)*averagedCoefficients P mainFactor (fun _=>1)
        (fun j=>(V/C)*amain j*(V/C)^(alpha j)/reference q V C Z allowance)
        (fun p i χ j=>(V/C)*localErrorCost p (errorIndex i)*aerror p i χ j*
          (V/C/(normValue p)^(errorIndex i+1))^(alpha j)/reference q V C Z allowance) j := by
  have hx:0<V/C:=div_pos hV hC
  have hnorm:∀p:O,0≤normValue p:=by intro p;unfold normValue;positivity
  intro j
  have hden:reference q V C Z allowance≠0:=by unfold reference;positivity
  have he:CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
      (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C^eps*(b^N)^(alpha j)*((V/C)*sourceCoefficients P mainFactor amain aerror alpha j*
        (V/C)^(alpha j)/reference q V C Z allowance):=by
    unfold CenteredMomentFirstCommonReferencePower.normalizedPower reference
    rw [Real.rpow_sub hx,Real.rpow_one,Real.rpow_neg hZ.le]
    field_simp
  rw [he]
  congr 1
  unfold sourceCoefficients averagedCoefficients
  simp only [one_mul]
  simp only [shortened_power (V/C) _ _ _ hx.le (hnorm _)]
  simp only [div_eq_mul_inv,mul_add,add_mul,Finset.mul_sum,Finset.sum_mul]
  ring_nf

theorem eventually_prime_average_gates
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
    (Sbad:Finset (Ideal O))(sigma primeLoss:ℝ)(hs:0<sigma)(hloss:0<primeLoss):
    ∀ᶠ Z:ℝ in Filter.atTop,1<Z ∧
      (primePool M H Sbad (1/2) 1 (Z^(sigma/3))).Nonempty ∧
      Z^(sigma/3-primeLoss)≤(primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card := by
  filter_upwards [eventually_actual_pool_card M H hH Sbad (sigma/3) primeLoss (by positivity) hloss,
    Filter.eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_,hc⟩
  apply Finset.card_pos.mp
  exact_mod_cast (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/3-primeLoss)).trans_le hc

lemma source_coefficients_nonneg (P:Finset (Ideal O))(mainFactor:ℝ)(hmain:0≤mainFactor)
    (amain:Fin 4→ℝ)(aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ)
    (ha:∀j,0≤amain j)(he:∀p i χ j,0≤aerror p i χ j):
    ∀j,0≤sourceCoefficients P mainFactor amain aerror alpha j := by
  intro j
  have hc:∀p:O,∀n:ℕ,0≤localErrorCost p n:=by
    intro p n
    have hn:0≤normValue p:=by unfold normValue;positivity
    unfold localErrorCost
    split <;> positivity
  unfold sourceCoefficients
  apply mul_nonneg (by positivity)
  apply add_nonneg (mul_nonneg hmain (ha j))
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (mul_nonneg (by positivity) (hc p (errorIndex i)))
  apply Finset.sum_nonneg
  intro χ _
  exact mul_nonneg (he p i χ j) (Real.rpow_nonneg (by unfold normValue;positivity) _)

def mainPowers (q Z Kmain ell deficit paid saving r:ℝ):Fin 4→ℝ:=
  ![q*Z^(ell+deficit/6+paid),Kmain^((5:ℝ)/6)*Z^(-2*max r 0/3),Kmain,Kmain*Z^(-saving)]

def errorPowers (p:O)(k:ℕ)(q Z Kerror deficit paid saving r:ℝ):Fin 4→ℝ:=
  ![q*Z^(errorMoving p Z k)*Z^(errorRemoval p Z k+deficit/6+paid),
    Kerror^((5:ℝ)/6)*Z^(-2*max r 0/3),Kerror,Kerror*Z^(-saving)]

lemma main_core_power (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ):
    ∀j,mainCores q V C Z allowance Kmain ell deficit paid eps saving r j=
      (V/C)*mainPowers q Z Kmain ell deficit paid saving r j*
        (V/C)^(CenteredMomentSecondChildPowerBudget.powers eps j)/reference q V C Z allowance := by
  intro j
  fin_cases j <;> simp [mainCores,mainPowers,CenteredMomentSecondChildPowerBudget.powers] <;> ring

lemma error_core_power (p:O)(k:ℕ)(q V C Z allowance Kerror deficit paid eps saving r:ℝ):
    ∀j,errorCores p k q V C Z allowance Kerror deficit paid eps saving r j=
      (V/C)*localErrorCost p (k-1)*errorPowers p k q Z Kerror deficit paid saving r j*
        (V/C/(normValue p)^k)^(CenteredMomentSecondChildPowerBudget.powers eps j)/reference q V C Z allowance := by
  intro j
  fin_cases j <;> simp [errorCores,errorPowers,CenteredMomentSecondChildPowerBudget.powers] <;> ring

theorem actual_power_reference_identity (P:Finset (Ideal O))(mainFactor b V C q Z allowance eps:ℝ)
    (N:ℕ)(H:Fin 4→ℝ)(Kmain ell deficit paid saving rmain:ℝ)
    (Kerror rerror:elementPool P→Fin 3→Ray→ℝ)
    (hV:0<V)(hC:0<C)(hq:0<q)(hZ:0<Z):
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers q Z Kmain ell deficit paid saving rmain j;
    let aerror:=fun (p:elementPool P) (i:Fin 3) (χ:Ray) (j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) q Z (Kerror p i χ) deficit paid saving (rerror p i χ) j;
    ∀j,CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
      (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C^eps*(b^N)^(alpha j)*averagedCoefficients P mainFactor H
        (mainCores q V C Z allowance Kmain ell deficit paid eps saving rmain)
        (fun p i χ=>errorCores p (errorIndex i+1) q V C Z allowance (Kerror p i χ)
          deficit paid eps saving (rerror p i χ)) j := by
  dsimp only
  intro j
  rw [source_normalized_identity P mainFactor b V C q Z allowance eps N _ _ _ hV hC hq hZ j]
  congr 1
  unfold averagedCoefficients
  simp only [one_mul]
  rw [main_core_power]
  congr 2
  · ring
  · apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro χ _
    rw [error_core_power]
    simp only [Nat.add_sub_cancel]
    ring

end SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

end

end OAI
