import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowFiniteFourier

namespace OAI

/-! Chinese-remainder factorization of the perfect residue Fourier pairing. -/
noncomputable section
namespace CubicFirstMoment

lemma residueFourierChar_mix {a b : Eisenstein} (ha : a≠0) (hb : b≠0)
    (h : Eisenstein) (v : Residues a × Residues b) :
    residueFourierChar (a*b) (mul_ne_zero ha hb)
        (Ideal.Quotient.mk (modulus (a*b)) h*residueMix a b v)=
      residueFourierChar a ha (Ideal.Quotient.mk (modulus a) h*v.1)*
        residueFourierChar b hb (Ideal.Quotient.mk (modulus b) h*v.2) := by
  rw [residueMix,← map_mul,residueFourierChar_mk,
    residueFourierChar_mk_mul,residueFourierChar_mk_mul]
  have haC : (a:ℂ)≠0 := fun hz => ha (Subtype.ext hz)
  have hbC : (b:ℂ)≠0 := fun hz => hb (Subtype.ext hz)
  have he : ((h*(b*residueRepresentative a v.1+a*residueRepresentative b v.2):Eisenstein):ℂ)*
      (1/(((a*b:Eisenstein):ℂ)*traceLambda))=
      (residueRepresentative a v.1:ℂ)*((h:ℂ)/((a:ℂ)*traceLambda))+
        (residueRepresentative b v.2:ℂ)*((h:ℂ)/((b:ℂ)*traceLambda)) := by
    push_cast
    field_simp [haC,hbC,traceLambda_ne_zero]
  have ht : tracePair ((h*(b*residueRepresentative a v.1+a*residueRepresentative b v.2):Eisenstein):ℂ)
      (1/(((a*b:Eisenstein):ℂ)*traceLambda))=
      tracePair (residueRepresentative a v.1:ℂ) ((h:ℂ)/((a:ℂ)*traceLambda))+
        tracePair (residueRepresentative b v.2:ℂ) ((h:ℂ)/((b:ℂ)*traceLambda)) := by
    unfold tracePair
    rw [he,Complex.add_re,mul_add]
  rw [ht,AddChar.map_add_eq_mul,Circle.coe_mul]

end CubicFirstMoment

end

end OAI
