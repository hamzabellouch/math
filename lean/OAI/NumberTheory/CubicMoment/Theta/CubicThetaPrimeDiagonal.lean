import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCharacterNontrivial

namespace OAI

/-! The full residue-unit diagonal quotient of the prime arithmetic
subgroup. Surjectivity is proved by completing primary primitive rows. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeIwahoriDiagonal {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeIwahori p →* (Residues p)ˣ where
  toFun g := (residue_isUnit_of_isCoprime
    (cubicThetaPrimeIwahori_diagonal_coprime hp g)).unit
  map_one' := by
    apply Units.ext
    simp only [IsUnit.unit_spec]
    change Ideal.Quotient.mk (modulus p) 1=1
    exact map_one _
  map_mul' g h := by
    apply Units.ext
    simp only [Units.val_mul,IsUnit.unit_spec,←map_mul]
    apply residue_eq_of_dvd_sub
    change p∣(g.val.val*h.val.val) 0 0-(g.val.val 0 0)*(h.val.val 0 0)
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      add_sub_cancel_left]
    exact dvd_mul_of_dvd_right h.property _

@[simp] lemma cubicThetaPrimeIwahoriDiagonal_coe {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) :
    (cubicThetaPrimeIwahoriDiagonal hp g : Residues p)=
      Ideal.Quotient.mk (modulus p) (g.val.val 0 0) := IsUnit.unit_spec _

theorem cubicThetaPrimeIwahoriDiagonal_surjective {p : Eisenstein} (hp : primaryPrime p) :
    Function.Surjective (cubicThetaPrimeIwahoriDiagonal hp) := by
  intro u
  let v := residueRepresentative p ((u⁻¹ : (Residues p)ˣ) : Residues p)
  obtain ⟨d,hd,hdp⟩ := residue_crt_one (primary_coprime_three hp.1) v
  have hdu : Ideal.Quotient.mk (modulus p) d=(u⁻¹ : (Residues p)ˣ) :=
    (residue_eq_of_dvd_sub hd).trans (residueRepresentative_spec _ _)
  have hpd : IsCoprime p d := isCoprime_of_residue_isUnit (by rw [hdu]; exact (u⁻¹).isUnit)
  let r : CubicThetaBottomRow :=
    ⟨3*p,d,dvd_mul_right 3 p,hdp,(primary_coprime_three hdp).symm.mul_left hpd⟩
  let g : cubicThetaPrimeIwahori p :=
    ⟨r.completion,by
      have hc := congrArg CubicThetaBottomRow.c r.completion_row
      change p∣r.completion.val 1 0
      change r.completion.val 1 0=3*p at hc
      rw [hc]
      exact dvd_mul_left p 3⟩
  refine ⟨g,?_⟩
  have hr := congrArg CubicThetaBottomRow.d r.completion_row
  change r.completion.val 1 1=d at hr
  have he : p∣(g.val.val 0 0)*d-1 := by
    have hg := cubicThetaPrincipalGroup_det g.val
    rw [show g.val.val 1 1=d from hr] at hg
    rw [show (g.val.val 0 0)*d-1=(g.val.val 0 1)*(g.val.val 1 0) by
      linear_combination hg]
    exact dvd_mul_of_dvd_right g.property _
  have hu : cubicThetaPrimeIwahoriDiagonal hp g*u⁻¹=1 := by
    apply Units.ext
    simp only [Units.val_mul,cubicThetaPrimeIwahoriDiagonal_coe,Units.val_one]
    rw [←hdu,←map_mul]
    exact (residue_eq_of_dvd_sub he).trans (map_one _)
  exact mul_inv_eq_one.mp hu

lemma cubicThetaPrimeIwahoriCharacter_diagonal {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) :
    cubicThetaPrimeIwahoriCharacter p hp g=
      cubicResidueChar p hp (cubicThetaPrimeIwahoriDiagonal hp g) := by
  rw [cubicThetaPrimeIwahoriDiagonal_coe,cubicResidueChar_mk]
  exact cubicSymbol_prime hp _

end CubicFirstMoment

end

end OAI
