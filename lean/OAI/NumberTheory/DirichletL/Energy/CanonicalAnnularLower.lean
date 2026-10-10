import OAI.NumberTheory.DirichletL.Energy.CanonicalAnnularPower

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyCanonicalAnnularLower
open HeckeFamily CanonicalQuadraticSieve CompletedGauss CenteredMomentCanonicalFirst
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstAmplificationChoice
open CenteredMomentPrimeElements CenteredMomentSectorLocalization
open CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentFirstChildProfileControl
open CenteredMomentSecondChildPowerBudget
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma parent_lower_ge {ι:Type*}[Fintype ι](s:Input ι)(Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    r≤parentLower s Z:=by
  have h (x:ℝ)(hx:Z^r≤x):r≤Real.logb Z x:=by
    have hh:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) r) hx
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  exact le_min (le_min (h _ hX₁) (h _ hX₂)) (le_min (h _ hY₁) (h _ hY₂))

lemma exceptional_cap_antitone (Z r s:ℝ)(hZ:1≤Z)(hrs:r≤s):
    Z^(-2*max s 0/3)≤Z^(-2*max r 0/3):=by
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hm:=max_le_max_right 0 hrs
  linarith

lemma main_powers_antitone (q Z K ell deficit paid saving r s:ℝ)
    (hZ:1≤Z)(hK:0≤K)(hrs:r≤s):
    ∀j,mainPowers q Z K ell deficit paid saving s j≤mainPowers q Z K ell deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk,le_refl]
  exact mul_le_mul_of_nonneg_left (exceptional_cap_antitone Z r s hZ hrs) (Real.rpow_nonneg hK _)

lemma error_powers_antitone (p:O)(k:ℕ)(q Z K deficit paid saving r s:ℝ)
    (hZ:1≤Z)(hK:0≤K)(hrs:r≤s):
    ∀j,errorPowers p k q Z K deficit paid saving s j≤errorPowers p k q Z K deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [errorPowers,Matrix.cons_val,Fin.reduceFinMk,le_refl]
  exact mul_le_mul_of_nonneg_left (exceptional_cap_antitone Z r s hZ hrs) (Real.rpow_nonneg hK _)

lemma source_coefficients_mono (P:Finset (Ideal O))(mainFactor:ℝ)(hf:0≤mainFactor)
    (am bm:Fin 4→ℝ)(ae be:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ)
    (hm:∀j,am j≤bm j)(he:∀p i χ j,ae p i χ j≤be p i χ j):
    ∀j,sourceCoefficients P mainFactor am ae alpha j≤sourceCoefficients P mainFactor bm be alpha j:=by
  intro j
  unfold sourceCoefficients
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add (mul_le_mul_of_nonneg_left (hm j) hf)
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by positivity) (CenteredMomentAmplificationErrorEnergy.localErrorCost_nonneg p (errorIndex i)))
  apply Finset.sum_le_sum
  intro χ _
  exact mul_le_mul_of_nonneg_right (he p i χ j)
    (Real.rpow_nonneg (pow_nonneg (by unfold normValue;positivity) _) _)

theorem actual_source_coefficients_lower {ι:Type*}[Fintype ι]
    (src:Input ι)(P:Finset (Ideal O))(C D:Ideal O)(E:Finset (CommonIndex C D))
    (K Z sigma delta reserve Mamp q deficit paid saving r:ℝ)
    (hZ:1<Z)(hsigma:0<sigma)(hMamp:0≤Mamp)
    (hX₁:Z^r≤src.X₁)(hX₂:Z^r≤src.X₂)(hY₁:Z^r≤src.Y₁)(hY₂:Z^r≤src.Y₂)
    (Hcoef:Fin 4→ℝ)(hH:∀j,0≤Hcoef j)(alpha:Fin 4→ℝ):
    let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve;
    let Kerr:=fun p:elementPool P=>fun i:Fin 3=>errorRadius C D E K (volume src) Z sigma delta reserve p (errorIndex i+1);
    let oldr:=parentLower src Z-Real.logb Z (C.absNorm:ℝ);
    let newr:=r-Real.logb Z (C.absNorm:ℝ);
    ∀j,sourceCoefficients P ((Mamp+2*sigma)/(sigma/6))
      (fun j=>Hcoef j*mainPowers q Z Kmain (sigma/3) deficit paid saving oldr j)
      (fun p i _χ j=>Hcoef j*errorPowers p (errorIndex i+1) q Z (Kerr p i) deficit paid saving
        (oldr-errorRemoval p Z (errorIndex i+1)) j) alpha j≤
    sourceCoefficients P ((Mamp+2*sigma)/(sigma/6))
      (fun j=>Hcoef j*mainPowers q Z Kmain (sigma/3) deficit paid saving newr j)
      (fun p i _χ j=>Hcoef j*errorPowers p (errorIndex i+1) q Z (Kerr p i) deficit paid saving
        (newr-errorRemoval p Z (errorIndex i+1)) j) alpha j:=by
  dsimp only
  have hr:=parent_lower_ge src Z r hZ hX₁ hX₂ hY₁ hY₂
  apply source_coefficients_mono P _ (by positivity)
  · intro j
    exact mul_le_mul_of_nonneg_left (main_powers_antitone q Z _ _ _ _ _ _ _ hZ.le
      (by unfold mainRadius CenteredMomentAmplifiedRetainedRadius.mainCommonRadius;positivity)
      (sub_le_sub_right hr _) j) (hH j)
  · intro p i χ j
    exact mul_le_mul_of_nonneg_left (error_powers_antitone p (errorIndex i+1) q Z _ _ _ _ _ _ hZ.le
      (by unfold errorRadius CenteredMomentAmplifiedRetainedRadius.errorCommonRadius;positivity)
      (sub_le_sub_right (sub_le_sub_right hr _) _) j) (hH j)

theorem actual_high_annular_sum {ι:Type*}[Fintype ι]
    (src:Input ι)(P:Finset (Ideal O))(C D R:Ideal O)(E:Finset (CommonIndex C D))
    (B:actualAllocations src.pools C)(τ:Character)(t:ℝ)
    (K Z sigma delta reserve Mamp deficit paid saving Mwidth eps:ℝ)
    (hZ:1<Z)(hsigma:0<sigma)(hMamp:0≤Mamp)
    (hX₁:Z^(Mwidth/4)≤src.X₁)(hX₂:Z^(Mwidth/4)≤src.X₂)
    (hY₁:Z^(Mwidth/4)≤src.Y₁)(hY₂:Z^(Mwidth/4)≤src.Y₂)
    (Hcoef:Fin 4→ℝ)(hH:∀j,0≤Hcoef j):
    let input:=child src C R B τ t;
    let q:ℝ:=τ.modulus.absNorm;
    let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve;
    let Kerr:=fun p:elementPool P=>fun i:Fin 3=>errorRadius C D E K (volume src) Z sigma delta reserve p (errorIndex i+1);
    let oldr:=parentLower src Z-Real.logb Z (C.absNorm:ℝ);
    let newr:=Mwidth/4-Real.logb Z (C.absNorm:ℝ);
    (∑j,sourceCoefficients P ((Mamp+2*sigma)/(sigma/6))
      (fun j=>Hcoef j*mainPowers q Z Kmain (sigma/3) deficit paid saving oldr j)
      (fun p i _χ j=>Hcoef j*errorPowers p (errorIndex i+1) q Z (Kerr p i) deficit paid saving
        (oldr-errorRemoval p Z (errorIndex i+1)) j) (powers eps) j*
      (volume input)^(powers eps j))*mass input^2≤
    (∑j,sourceCoefficients P ((Mamp+2*sigma)/(sigma/6))
      (fun j=>Hcoef j*mainPowers q Z Kmain (sigma/3) deficit paid saving newr j)
      (fun p i _χ j=>Hcoef j*errorPowers p (errorIndex i+1) q Z (Kerr p i) deficit paid saving
        (newr-errorRemoval p Z (errorIndex i+1)) j) (powers eps) j*
      (volume input)^(powers eps j))*mass input^2:=by
  dsimp only
  have h:=actual_source_coefficients_lower src P C D E K Z sigma delta reserve Mamp
    (τ.modulus.absNorm:ℝ) deficit paid saving (Mwidth/4) hZ hsigma hMamp hX₁ hX₂ hY₁ hY₂
    Hcoef hH (powers eps)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_right (h j)
    (Real.rpow_nonneg (volume_pos _).le _))

end SevenEighths.CenteredMomentEnergyCanonicalAnnularLower

end

end OAI
