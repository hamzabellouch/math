import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalBudget
import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving
open HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid IdealMobiusDivisorSum
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondExceptionalOriginalBlock CenteredMomentSecondExceptionalBudget
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalAllowance
open CenteredMomentRankinRadical
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma column_power_saving (Z c d θ:ℝ) (hZ:1<Z) (hc:1≤c) (hd:1≤d) (hθ:θ≤1/3) :
    (c*d)^θ*Z^(-(Real.logb Z c+Real.logb Z d)/3)≤1 := by
  have hc0:0<c:=zero_lt_one.trans_le hc
  have hd0:0<d:=zero_lt_one.trans_le hd
  have hz:0<Z:=zero_lt_one.trans hZ
  have he:-(Real.logb Z c+Real.logb Z d)/3=Real.logb Z (c*d)*(-1/3):=by
    rw [Real.logb_mul hc0.ne' hd0.ne'];ring
  rw [he,Real.rpow_mul hz.le,Real.rpow_logb hz (ne_of_gt hZ) (mul_pos hc0 hd0),
    ←Real.rpow_add (mul_pos hc0 hd0)]
  have hcd:1≤c*d:=by nlinarith
  exact (Real.rpow_le_rpow_of_exponent_le hcd (by linarith : θ+ -1/3≤0)).trans_eq
    (Real.rpow_zero _)

lemma forcingNorm_ge_one (C D:Ideal O)(hC:Supported C)(U:Finset (CommonIndex C D)) :
    1≤forcingNorm C D U := by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold forcingNorm at hf ⊢
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hf)

theorem original_budget_physical_saving_full
    (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys a:ℝ)(n:Fin 4→ℤ)(hK:0≤K)(hZ:1<Z)
    (hKphys:0<Kphys)(ha:0<a)
    (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(hrows:∀z∈rows,z≠0)(W:𝓢(ℝ,ℂ))
    (hlower:∀I:Ideal O,β I≠0→a*volume s.toData≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W Kphys n≠0) :
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      ((volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ))*
      Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
      (Ideal.absNorm (commonRadical C D):ℝ) := by
  have hp:0<(Ideal.absNorm (commonRadical C D):ℝ):=by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf:=forcingNorm_ge_one C D hC U
  have hfp:1≤(forcingNorm C D U)^(1/3:ℝ):=Real.one_le_rpow hf (by norm_num)
  have hcost:=original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W Kphys n
    hKphys (volume s.toData) a Z (volume_pos s.toData) ha hZ hlower hne
  let A:ℝ:=profileFactor s p J Q K*
    Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ
  let E:ℝ:=(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
    Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)
  have hA:0≤A:=mul_nonneg
    (mul_nonneg (profileFactor_nonneg s p J Q K hK) (Real.rpow_nonneg (by linarith) _))
    (Real.rpow_nonneg (by positivity) _)
  have hv:=volume_pos s.toData
  have hz:0<Z:=zero_lt_one.trans hZ
  have hE:0≤E:=by dsimp [E];positivity
  rw [central_sourceBudget_exact s p J Q C D hC hD U K Z ε δ θ r Kphys n hZ,
    common_ideal_product]
  change A*centralPhysicalCost C D U Kphys (volume s.toData) n/
    ((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ))≤_
  calc
    _≤A*E/((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hA)
        (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _))
    _≤A*E/(Ideal.absNorm (commonRadical C D):ℝ):=by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hE) hp
      nlinarith
    _= _:=by dsimp [A,E];ring

lemma column_cap_ledger (c d r:ℝ)(hc:0≤c)(hd:0≤d) :
    2*max r 0/3≤(c+d)/3+max (r-min c d) 0 := by
  have hmin:0≤min c d:=le_min hc hd
  have hc':min c d≤c:=min_le_left _ _
  have hd':min c d≤d:=min_le_right _ _
  by_cases hr:0≤r
  · rw [max_eq_left hr]
    by_cases hm:r≤min c d
    · rw [max_eq_right (by linarith : r-min c d≤0)]
      linarith
    · rw [max_eq_left (by linarith : 0≤r-min c d)]
      linarith
  · rw [max_eq_right (le_of_not_ge hr)]
    have hm:0≤max (r-min c d) 0:=le_max_right _ _
    linarith

theorem original_budget_physical_saving
    (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys a:ℝ)(n:Fin 4→ℤ)(hK:0≤K)(hZ:1<Z)
    (hKphys:0<Kphys)(ha:0<a)(hθ:θ≤1/3)
    (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(hrows:∀z∈rows,z≠0)(W:𝓢(ℝ,ℂ))
    (hlower:∀I:Ideal O,β I≠0→a*volume s.toData≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W Kphys n≠0) :
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
      (Ideal.absNorm (commonRadical C D):ℝ) := by
  have hc:1≤(C.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hp:0<(Ideal.absNorm (commonRadical C D):ℝ):=by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf:=forcingNorm_ge_one C D hC U
  have hfp:1≤(forcingNorm C D U)^(1/3:ℝ):=Real.one_le_rpow hf (by norm_num)
  have hcost:=original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W Kphys n
    hKphys (volume s.toData) a Z (volume_pos s.toData) ha hZ hlower hne
  have hcol:=column_power_saving Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ hZ hc hd hθ
  let A:ℝ:=profileFactor s p J Q K*
    Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)
  let E:ℝ:=(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)
  have hA:0≤A:=mul_nonneg (profileFactor_nonneg s p J Q K hK) (Real.rpow_nonneg (by linarith) _)
  have hv:=volume_pos s.toData
  have hE:0≤E:=by dsimp [E];positivity
  have hnum:A*((C.absNorm:ℝ)*D.absNorm)^θ*centralPhysicalCost C D U Kphys (volume s.toData) n≤A*E:=by
    calc
      _≤A*((C.absNorm:ℝ)*D.absNorm)^θ*
          (E*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
        exact mul_le_mul_of_nonneg_left hcost (mul_nonneg hA (Real.rpow_nonneg (by positivity) _))
      _=A*E*(((C.absNorm:ℝ)*D.absNorm)^θ*
          Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by ring
      _≤A*E*1:=mul_le_mul_of_nonneg_left hcol (mul_nonneg hA hE)
      _=A*E:=mul_one _
  rw [central_sourceBudget_exact s p J Q C D hC hD U K Z ε δ θ r Kphys n hZ,
    common_ideal_product]
  change A*((C.absNorm:ℝ)*D.absNorm)^θ*centralPhysicalCost C D U Kphys (volume s.toData) n/
    ((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ))≤_
  calc
    _≤A*E/((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=
      div_le_div_of_nonneg_right hnum (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _))
    _≤A*E/(Ideal.absNorm (commonRadical C D):ℝ):=by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hE) hp
      nlinarith
    _= _:=by dsimp [A,E];ring

end SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving

end

end OAI
