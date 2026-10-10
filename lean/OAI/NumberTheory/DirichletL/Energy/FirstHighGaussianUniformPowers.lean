import OAI.NumberTheory.DirichletL.Energy.FirstGaussianProfileWeights
import OAI.NumberTheory.DirichletL.Energy.FirstHighNormalizedGaussianPowers

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentSecondChildPowerBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

lemma finite_power_budget (upper nc Z eps Bcommon deficit primeLoss G F seed:ℝ)
    (N:ℕ)(hupper:1≤upper)(hnc:0≤nc)(hZ:1<Z)(heps:0≤eps)(heps1:eps≤1)
    (hncap:nc≤Z^Bcommon)(hG:0≤G)(_hF:0≤F)(_hseed:0<seed)
    (H srcLoss actualLoss:Fin 4→ℝ)(hH:∀j,0≤H j)
    (hbound:∀j,H j≤F*Z^(srcLoss j)/seed):
    nc^eps*(∑j:Fin 4,(upper^N)^(powers eps j)*
      (G*H j*Z^(deficit+actualLoss j+primeLoss)))≤
      (upper^N*G*F/seed)*Z^(deficit+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+actualLoss j):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hncPow:nc^eps≤Z^(eps*Bcommon):=by
    have hh:=Real.rpow_le_rpow hnc hncap heps
    simpa only [←Real.rpow_mul hz.le,mul_comm Bcommon eps] using hh
  have hu:1≤upper^N:=one_le_pow₀ hupper
  have hup (j:Fin 4):(upper^N)^(powers eps j)≤upper^N:=by
    have hp:powers eps j≤1:=by fin_cases j <;> simp [powers] <;> linarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hu hp
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj0:=hH j
  have hu0:0≤upper:=zero_le_one.trans hupper
  calc
    _≤Z^(eps*Bcommon)*(upper^N*(G*(F*Z^(srcLoss j)/seed)*Z^(deficit+actualLoss j+primeLoss))):=by
      apply mul_le_mul hncPow _ (by positivity) (by positivity)
      apply mul_le_mul (hup j) _ (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left (hbound j) hG
    _=(upper^N*G*F/seed)*Z^(deficit+eps*Bcommon+primeLoss)*Z^(srcLoss j+actualLoss j):=by
      calc
        _=(upper^N*G*F/seed)*(Z^(eps*Bcommon)*Z^(srcLoss j)*Z^(deficit+actualLoss j+primeLoss)):=by ring
        _=_:=by
          rw [←Real.rpow_add hz, ←Real.rpow_add hz]
          rw [show eps*Bcommon + srcLoss j + (deficit+actualLoss j+primeLoss) =
            (deficit+eps*Bcommon+primeLoss)+(srcLoss j+actualLoss j) by ring,
            Real.rpow_add hz]
          ring

theorem actual_high_uniform_four_powers {a b:ℝ}
    (N:ℕ)(upper b1 b2 Amax loFloor:ℝ)
    (Cm Ce Cd Ct Cc cost epsilon deltaSource thetaSource Bcap:ℝ)
    (Jprofile Jchild degree:ℕ)(Sp Tchild Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:1≤upper)(hb1:0≤b1)(hb2:0≤b2)(hAmax:0≤Amax)(hlo:0<loFloor)
    (hCm:0≤Cm)(hCe:0≤Ce)(hCd:0≤Cd)(hCt:0≤Ct)(hCc:0≤Cc)(hcost:0≤cost)
    (sigma delta reserve paid saving Mcap Mamp primeLoss Bcommon:ℝ)
    (hs:0<sigma)(heps:0≤epsilon)(heps1:epsilon≤1)(hloss:0≤primeLoss)(hMamp:0≤Mamp):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀Q:Ideal O,∀Kfix:ℝ,0≤Kfix→∃Cbound:ℝ,0<Cbound ∧
    ∀p:Profiles a b,∀Z t height A seed C0 C1:ℝ,
      1<Z→0≤height→0≤A→A≤Amax→1≤seed→0≤C0→0≤C1→
    ∀(M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O)),
    fixedBadPrimes⊆Sbad→
    ∀(η τ:Character)(C D:Ideal O)(_hC:Supported C)(_hD:Supported D),
    primeSupport C=primeSupport D→∀E:Finset (CommonIndex C D),
    ∀K V Mdecl Mwidth:ℝ,0<K→0<V→0≤Mdecl→Mdecl≤Mcap→
    Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth→Mwidth≤Mdecl→
    Real.logb Z V≤Mdecl→
    Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card→
    τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}→
    (C.absNorm:ℝ)≤Z^Bcommon→
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (q:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve q (errorIndex i+1);
    let alpha:=powers epsilon;
    let Ebase:=Cc*(C0+C1)*diagonalControl W*(p.control Tchild)^2*(1+height)^degree;
    let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
      (fixedFactors Cm Ce Cd Ct Z epsilon deltaSource thetaSource Bcap cost Ebase t loFloor seed Jchild Sf W);
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j;
    let aerror:=fun (q:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers q (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror q i χ)
        (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval q Z (errorIndex i+1)) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) epsilon
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (Cbound*(C0+C1+1)*(p.control U)^2*(1+|t|+height)^J/seed)*
        Z^(Mdecl-M0+epsilon*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(losses epsilon deltaSource thetaSource Bcap j+
          lossVector sigma delta reserve paid epsilon Mcap saving j):=by
  obtain ⟨U,J,hweights⟩:=actual_weights N upper b1 b2 Amax loFloor
    Cm Ce Cd Ct Cc cost epsilon deltaSource thetaSource Bcap Jprofile Jchild degree Sp Tchild Sf W
    (zero_le_one.trans hu) hb1 hb2 hAmax hlo hCm hCe hCd hCt hCc hcost
  refine ⟨U,J,?_⟩
  intro Q Kfix hKfix
  obtain ⟨Cweights,hCweights,hw⟩:=hweights Q Kfix hKfix
  let G:=56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))
  have hG:0<G:=by dsimp [G];positivity
  refine ⟨upper^N*G*Cweights,by positivity,?_⟩
  intro p Z t height A seed C0 C1 hZ hheight hA hAA hseed hC0 hC1
    M _ Hray Sbad hbad η τ C D hC hD hCD E K V Mdecl Mwidth hK hV hM hcap hactual hwidth hlow hcard hmod hncap
  dsimp only
  let Ebase:=Cc*(C0+C1)*diagonalControl W*(p.control Tchild)^2*(1+height)^degree
  let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
    (fixedFactors Cm Ce Cd Ct Z epsilon deltaSource thetaSource Bcap cost Ebase t loFloor seed Jchild Sf W)
  have hEbase:0≤Ebase:=by
    have hd:=diagonalControl_nonneg W
    dsimp [Ebase]
    positivity
  have hH:∀j,0≤H j:=coefficients_nonneg N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed _
    (zero_le_one.trans hu) hb1 hb2 hKfix (zero_le_one.trans hseed)
    (fixedFactors_nonneg Cm Ce Cd Ct Z epsilon deltaSource thetaSource Bcap cost Ebase t loFloor seed Jchild Sf W
      hCm hCe hCd hCt (zero_le_one.trans hZ.le) hcost hEbase hlo.le (zero_le_one.trans hseed))
  have ha:=CenteredMomentEnergyFirstHighNormalizedGaussianPowers.actual_high_normalized_four_powers
    M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid epsilon saving Mdecl Mwidth Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hwidth hlow hloss hMamp hcard hmod upper N (zero_le_one.trans hu)
    H hH
  dsimp only at ha
  apply ha.trans
  have hb:=finite_power_budget upper (C.absNorm:ℝ) Z epsilon Bcommon
    (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) primeLoss G
    (Cweights*(C0+C1+1)*(p.control U)^2*(1+|t|+height)^J) seed N hu (Nat.cast_nonneg _)
    hZ heps heps1 hncap hG.le (by positivity) (zero_lt_one.trans_le hseed) H
    (losses epsilon deltaSource thetaSource Bcap)
    (lossVector sigma delta reserve paid epsilon Mcap saving) hH
    (hw p Z t height A seed C0 C1 (zero_lt_one.trans hZ) hheight hA hAA hseed hC0 hC1)
  convert hb using 1 ; dsimp only [G] ; ring

theorem actual_high_homogeneous_four_powers
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth)(hwidth:Mwidth≤Mdecl)
    (hlow:Real.logb Z V≤Mdecl)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:1≤upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)
    (F seed Bcommon:ℝ)(srcLoss:Fin 4→ℝ)(hF:0≤F)(hseed:0<seed)(heps1:eps≤1)
    (hncap:(C.absNorm:ℝ)≤Z^Bcommon)
    (hbound:∀j,H j≤F*Z^(srcLoss j)/seed):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1)) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (upper^N*(56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ)))*F/seed)*
        Z^(Mdecl-M0+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+lossVector sigma delta reserve paid eps Mcap saving j) := by
  have ha:=CenteredMomentEnergyFirstHighNormalizedGaussianPowers.actual_high_normalized_four_powers
    M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hwidth hlow hloss hMamp hcard hmod
    upper N (zero_le_one.trans hupper) H hH
  dsimp only at ha ⊢
  apply ha.trans
  exact finite_power_budget upper (C.absNorm:ℝ) Z eps Bcommon
    (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) primeLoss
    (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))) F seed N
    hupper (Nat.cast_nonneg _) hZ heps heps1 hncap (by positivity) hF hseed H
    srcLoss (lossVector sigma delta reserve paid eps Mcap saving) hH hbound

end SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers

end

end OAI
