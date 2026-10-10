import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCubeConstant
import OAI.NumberTheory.CubicMoment.Estimates.IdealThetaLattice

namespace OAI

/-! Every nonzero cubic Eisenstein integer has exactly one ideal exponent
vector and one of two signs. This removes the cube-root multiplicity. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eisenstein_unit_cube_sign (u : Eisensteinˣ) :
    (u:Eisenstein)^3=1 ∨ (u:Eisenstein)^3 = -1 := by
  obtain ⟨j,hj | hj⟩ := eisenstein_unit_eq_signed_omega u.isUnit
  · left
    rw [hj,←pow_mul,Nat.mul_comm j 3,pow_mul,omegaE_cube,one_pow]
  · right
    rw [hj,neg_pow,←pow_mul,Nat.mul_comm j 3,pow_mul,omegaE_cube,one_pow]
    norm_num

def cubicThetaSignedCube (ε : Bool) (ν : EisensteinIdealExponent) : Eisenstein :=
  if ε then -(idealExponentGenerator ν)^3 else (idealExponentGenerator ν)^3

lemma cubicThetaSignedCube_ne_zero (ε : Bool) (ν : EisensteinIdealExponent) :
    cubicThetaSignedCube ε ν≠0 := by
  cases ε <;> simp [cubicThetaSignedCube,idealExponentGenerator_ne_zero]

lemma cubicThetaSignedCube_is_cube (ε : Bool) (ν : EisensteinIdealExponent) :
    ∃ j : Eisenstein, j^3=cubicThetaSignedCube ε ν := by
  cases ε
  · exact ⟨idealExponentGenerator ν,rfl⟩
  · exact ⟨-idealExponentGenerator ν,by change (-idealExponentGenerator ν)^3=-(idealExponentGenerator ν)^3; ring⟩

lemma cubicTheta_idealExponentOf_neg {a : Eisenstein} (ha : a≠0) :
    idealExponentOf (-a)=idealExponentOf a :=
  idealExponentOf_eq_of_associated (neg_ne_zero.mpr ha) ha (Associated.refl a).neg_left

lemma cubicThetaSignedCube_exponent (ε : Bool) (ν : EisensteinIdealExponent) :
    idealExponentOf (cubicThetaSignedCube ε ν)=3•ν := by
  cases ε <;> simp only [cubicThetaSignedCube,Bool.false_eq_true,ite_false,ite_true]
  · rw [idealExponentOf_pow (idealExponentGenerator_ne_zero ν),idealExponentOf_generator]
  · rw [cubicTheta_idealExponentOf_neg (pow_ne_zero _ (idealExponentGenerator_ne_zero ν)),
      idealExponentOf_pow (idealExponentGenerator_ne_zero ν),idealExponentOf_generator]

abbrev CubicThetaNonzeroCube := {c : Eisenstein // c≠0 ∧ ∃ j : Eisenstein, j^3=c}

def cubicThetaCubeCoordinatesMap (x : Bool × EisensteinIdealExponent) : CubicThetaNonzeroCube :=
  ⟨cubicThetaSignedCube x.1 x.2,cubicThetaSignedCube_ne_zero x.1 x.2,
    cubicThetaSignedCube_is_cube x.1 x.2⟩

lemma cubicThetaCubeCoordinates_bijective : Function.Bijective cubicThetaCubeCoordinatesMap := by
  constructor
  · rintro ⟨ε,ν⟩ ⟨δ,κ⟩ he
    have hv := congrArg (fun x : CubicThetaNonzeroCube => idealExponentOf x.val) he
    change idealExponentOf (cubicThetaSignedCube ε ν)=
      idealExponentOf (cubicThetaSignedCube δ κ) at hv
    rw [cubicThetaSignedCube_exponent,cubicThetaSignedCube_exponent] at hv
    have hν : ν=κ := by
      ext p
      have hp := congrArg (fun f : EisensteinIdealExponent => f p) hv
      simp only [Finsupp.smul_apply,smul_eq_mul] at hp
      omega
    subst κ
    have he' := congrArg Subtype.val he
    change cubicThetaSignedCube ε ν=cubicThetaSignedCube δ ν at he'
    have hn := pow_ne_zero 3 (idealExponentGenerator_ne_zero ν)
    have htwo : (2:Eisenstein)≠0 := by norm_num
    have hcontra : ¬ -(idealExponentGenerator ν)^3=(idealExponentGenerator ν)^3 := by
      intro h
      have hz : (2:Eisenstein)*(idealExponentGenerator ν)^3=0 := by linear_combination -h
      exact (mul_ne_zero htwo hn) hz
    cases ε <;> cases δ
    · rfl
    · exact False.elim (hcontra (by simpa only [cubicThetaSignedCube,ite_true,ite_false,
        Bool.false_eq_true] using he'.symm))
    · exact False.elim (hcontra (by simpa only [cubicThetaSignedCube,ite_true,ite_false,
        Bool.false_eq_true] using he'))
    · rfl
  · intro c
    obtain ⟨j,hj⟩ := c.property.2
    have hj0 : j≠0 := by intro h; subst j; simp at hj; exact c.property.1 hj.symm
    let ν := idealExponentOf j
    obtain ⟨u,hu⟩ := idealExponentOf_associated hj0
    rcases eisenstein_unit_cube_sign u with hs | hs
    · refine ⟨(false,ν),Subtype.ext ?_⟩
      change (idealExponentGenerator ν)^3=c.val
      rw [←hj,←hu,mul_pow,hs,mul_one]
    · refine ⟨(true,ν),Subtype.ext ?_⟩
      change -(idealExponentGenerator ν)^3=c.val
      rw [←hj,←hu,mul_pow,hs,mul_neg_one]

def cubicThetaCubeCoordinates : (Bool × EisensteinIdealExponent) ≃ CubicThetaNonzeroCube :=
  Equiv.ofBijective _ cubicThetaCubeCoordinates_bijective

lemma cubicThetaSignedCube_norm (ε : Bool) (ν : EisensteinIdealExponent) :
    norm (cubicThetaSignedCube ε ν)=idealExponentNorm ν^3 := by
  have hc : norm ((idealExponentGenerator ν)^3)=idealExponentNorm ν^3 := by
    rw [←normNat_cast,show normNat ((idealExponentGenerator ν)^3)=
      normNat (idealExponentGenerator ν)^3 from map_pow normNatHom _ _,Nat.cast_pow]
    rfl
  cases ε <;> simpa only [cubicThetaSignedCube,Bool.false_eq_true,ite_false,ite_true,
    norm,Eisenstein.coe_neg,Complex.normSq_neg] using hc

end CubicFirstMoment

end

end OAI
