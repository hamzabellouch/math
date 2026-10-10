import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryConstant
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUnitLifting
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedIdeal

namespace OAI

/-! The primary cubes at the inverted cusp are in exact bijection with
ideals prime to lambda. No choice of a cube root contributes multiplicity. -/
noncomputable section
namespace CubicFirstMoment

abbrev CubicThetaUnramifiedIdeal :=
  {ν : EisensteinIdealExponent // ν cubicThetaRamifiedPrime=0}

abbrev CubicThetaPrimaryCube :=
  {c : Eisenstein // primary c ∧ ∃ j : Eisenstein, j^3=c}

lemma cubicThetaPrimaryGenerator_primary (ν : CubicThetaUnramifiedIdeal) :
    primary (idealPrimaryGenerator ν.val) := by
  have hn : ¬lambdaE∣idealExponentGenerator ν.val := by
    rw [cubicThetaRamifiedPrime_dvd_iff,ν.property]
    exact Nat.not_lt_zero _
  have hc : IsCoprime (idealExponentGenerator ν.val) lambdaE :=
    (lambdaE_prime.coprime_iff_not_dvd.mpr hn).symm
  have hc3 : IsCoprime (idealExponentGenerator ν.val) 3 := by
    have ht := hc.pow_right (n:=2)
    rw [lambdaE_sq] at ht
    simpa using ht.neg_right
  exact primaryNormalize_primary (residue_isUnit_of_isCoprime hc3.symm)

lemma cubicThetaPrimaryGenerator_cube_primary (ν : CubicThetaUnramifiedIdeal) :
    primary ((idealPrimaryGenerator ν.val)^3) := by
  have hp := cubicThetaPrimaryGenerator_primary ν
  simpa only [pow_succ,pow_zero,one_mul] using primary_mul (primary_mul hp hp) hp

def cubicThetaPrimaryCubeMap (ν : CubicThetaUnramifiedIdeal) : CubicThetaPrimaryCube :=
  ⟨(idealPrimaryGenerator ν.val)^3,cubicThetaPrimaryGenerator_cube_primary ν,
    idealPrimaryGenerator ν.val,rfl⟩

lemma cubicThetaPrimaryCubeMap_exponent (ν : CubicThetaUnramifiedIdeal) :
    idealExponentOf (cubicThetaPrimaryCubeMap ν).val=3•ν.val := by
  rw [cubicThetaPrimaryCubeMap,idealExponentOf_pow
    (primary_ne_zero (cubicThetaPrimaryGenerator_primary ν)),idealExponentOf_primaryGenerator]

lemma cubicThetaPrimaryCubeMap_bijective : Function.Bijective cubicThetaPrimaryCubeMap := by
  constructor
  · intro ν κ he
    apply Subtype.ext
    have ht := congrArg (fun c : CubicThetaPrimaryCube => idealExponentOf c.val) he
    rw [cubicThetaPrimaryCubeMap_exponent,cubicThetaPrimaryCubeMap_exponent] at ht
    ext p
    have hp := congrArg (fun f : EisensteinIdealExponent => f p) ht
    simp only [Finsupp.smul_apply,smul_eq_mul] at hp
    omega
  · intro c
    obtain ⟨j,hj⟩ := c.property.2
    have hj0 : j≠0 := by
      intro h
      subst j
      have hc0 := primary_ne_zero c.property.1
      simp only [zero_pow (by norm_num : (3:ℕ)≠0)] at hj
      exact hc0 hj.symm
    let ν := idealExponentOf j
    have hν : ν cubicThetaRamifiedPrime=0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      have hd : lambdaE∣j :=
        ((cubicThetaRamifiedPrime_dvd_iff ν).mpr hpos).trans (idealExponentOf_associated hj0).dvd
      have hd' : lambdaE∣c.val := hj ▸ hd.trans (dvd_pow_self j (by norm_num : (3:ℕ)≠0))
      exact lambdaE_prime.not_isUnit ((primary_coprime_lambda c.property.1).isRelPrime hd' dvd_rfl)
    refine ⟨⟨ν,hν⟩,Subtype.ext ?_⟩
    change (idealPrimaryGenerator ν)^3=c.val
    apply primary_associated_eq (cubicThetaPrimaryGenerator_cube_primary ⟨ν,hν⟩) c.property.1
    rw [←hj]
    exact ((primaryNormalize_associated (idealExponentGenerator ν)).symm.trans
      (idealExponentOf_associated hj0)).pow_pow

def cubicThetaPrimaryCubeEquiv : CubicThetaUnramifiedIdeal ≃ CubicThetaPrimaryCube :=
  Equiv.ofBijective _ cubicThetaPrimaryCubeMap_bijective

lemma cubicThetaPrimaryCube_norm (ν : CubicThetaUnramifiedIdeal) :
    norm (cubicThetaPrimaryCubeMap ν).val=idealExponentNorm ν.val^3 := by
  change norm ((idealPrimaryGenerator ν.val)^3)=_
  rw [←normNat_cast,show normNat ((idealPrimaryGenerator ν.val)^3)=
    normNat (idealPrimaryGenerator ν.val)^3 from map_pow normNatHom _ _,
    Nat.cast_pow,normNat_cast,idealPrimaryGenerator_norm]

lemma cubicThetaPrimaryCube_units (ν : CubicThetaUnramifiedIdeal) :
    (Nat.card (Residues (cubicThetaPrimaryCubeMap ν).val)ˣ:ℂ)=
      (idealExponentNorm ν.val:ℂ)^2*(cubicThetaIdealTotient ν.val:ℂ) := by
  have hp0 := primary_ne_zero (cubicThetaPrimaryGenerator_primary ν)
  change (Nat.card (Residues ((idealPrimaryGenerator ν.val)^3))ˣ:ℂ)=_
  rw [show (3:ℕ)=2+1 from rfl,cubicTheta_power_units_card hp0 2,Nat.cast_mul,Nat.cast_pow]
  have hnorm : (normNat (idealPrimaryGenerator ν.val):ℂ)=(idealExponentNorm ν.val:ℂ) := by
    rw [←Complex.ofReal_natCast,normNat_cast,idealPrimaryGenerator_norm]
  have ht : Nat.card (Residues (idealPrimaryGenerator ν.val))ˣ=cubicThetaIdealTotient ν.val :=
    cubicTheta_residue_units_associated (primaryNormalize_associated (idealExponentGenerator ν.val)).symm
  rw [hnorm,ht]

end CubicFirstMoment

end

end OAI
