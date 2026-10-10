import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootBruhatOperators

namespace OAI

/-! Choice-independent nonzero Bruhat branches, indexed by the actual
prime residue units. The cubic multiplier is the original residue character. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootReciprocal (p : Eisenstein) (r : Residues p) : Residues p :=
  Ring.inverse (Ideal.Quotient.mk (modulus p) 9*r)

lemma cubicThetaPrimeRoot_nine_unit {p : Eisenstein} (hp : primaryPrime p) :
    IsUnit (Ideal.Quotient.mk (modulus p) 9) := by
  have hc : IsCoprime p (9:Eisenstein) := by
    convert (primary_coprime_three hp.1).pow_right (n:=2) using 1
    norm_num
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime hc
  rw [←hu]
  exact u.isUnit

lemma cubicThetaPrimeRootReciprocal_pair {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (hr : IsUnit r) :
    p∣9*residueRepresentative p (cubicThetaPrimeRootReciprocal p r)*residueRepresentative p r-1 := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk (modulus p)
    (9*residueRepresentative p (cubicThetaPrimeRootReciprocal p r)*residueRepresentative p r-1)=0
  rw [map_sub,map_one,sub_eq_zero]
  simp only [map_mul,residueRepresentative_spec,cubicThetaPrimeRootReciprocal]
  calc
    _ = Ring.inverse (Ideal.Quotient.mk (modulus p) 9*r)*
        (Ideal.Quotient.mk (modulus p) 9*r) := by ring
    _ = 1 := Ring.inverse_mul_cancel _ ((cubicThetaPrimeRoot_nine_unit hp).mul hr)

lemma cubicThetaPrimeRootBruhat_residue_character {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) :
    cubicSymbol p (3*residueRepresentative p r)=cubicSymbol p 3*cubicResidueChar p hp r := by
  rw [cubicSymbol_mul_upper hp.1]
  congr 1
  rw [cubicSymbol_prime hp,←cubicResidueChar_mk p hp,residueRepresentative_spec]

theorem cubicThetaPrimeRootWeyl_residue_branch {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (hr : IsUnit r) (F : CubicThetaSection) :
    cubicThetaPrimeRootWeylSection hp
      (cubicThetaPrimeRootResidueOperator hp r (cubicThetaPrimeRootSectionRestrict F))=
      (cubicSymbol p 3*cubicResidueChar p hp r) •
        cubicThetaPrimeRootResidueOperator hp (-cubicThetaPrimeRootReciprocal p r)
          (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F)) := by
  let x := residueRepresentative p (cubicThetaPrimeRootReciprocal p r)
  have hx : Ideal.Quotient.mk (modulus p) (-x)= -cubicThetaPrimeRootReciprocal p r := by
    rw [map_neg]
    exact congrArg Neg.neg (residueRepresentative_spec p _)
  rw [←hx,cubicThetaPrimeRootResidueOperator_mk]
  change cubicThetaPrimeRootWeylSection hp
    (cubicThetaPrimeRootSectionTranslate hp (residueRepresentative p r) (cubicThetaPrimeRootSectionRestrict F))=
      (cubicSymbol p 3*cubicResidueChar p hp r) • cubicThetaPrimeRootSectionTranslate hp (-x)
        (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F))
  rw [←cubicThetaPrimeRootBruhat_residue_character hp r]
  exact cubicThetaPrimeRootWeyl_translated_global hp x (residueRepresentative p r)
    (cubicThetaPrimeRootReciprocal_pair hp r hr) F

end CubicFirstMoment

end

end OAI
