import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueCRT

namespace OAI

/-! The inverse in the Kloosterman phase under the exact mixed-residue
parametrization. The two inverse-square twists are retained explicitly. -/
noncomputable section
namespace CubicFirstMoment

private lemma inverse_square_product {R : Type*} [CommRing R] (t x : R)
    (ht : IsUnit t) (hx : IsUnit x) :
    (t*x)*(t*((Ring.inverse t)^2*Ring.inverse x))=1 := by
  calc
    _ = (t*Ring.inverse t)^2*(x*Ring.inverse x) := by ring
    _ = 1 := by rw [Ring.mul_inverse_cancel t ht,Ring.mul_inverse_cancel x hx]; norm_num

theorem cubicThetaResidueMix_inverse {a b : Eisenstein} (ha : a≠0) (hb : b≠0)
    (hab : IsCoprime a b) (x : Residues a) (y : Residues b)
    (hx : IsUnit x) (hy : IsUnit y) :
    Ring.inverse (residueMix a b (x,y))=
      residueMix a b
        ((Ring.inverse (Ideal.Quotient.mk (modulus a) b))^2*Ring.inverse x,
          (Ring.inverse (Ideal.Quotient.mk (modulus b) a))^2*Ring.inverse y) := by
  have ht : IsUnit (Ideal.Quotient.mk (modulus a) b) := residue_isUnit_of_isCoprime hab
  have hu : IsUnit (Ideal.Quotient.mk (modulus b) a) := residue_isUnit_of_isCoprime hab.symm
  have hm : residueMix a b (x,y)*residueMix a b
        ((Ring.inverse (Ideal.Quotient.mk (modulus a) b))^2*Ring.inverse x,
          (Ring.inverse (Ideal.Quotient.mk (modulus b) a))^2*Ring.inverse y)=1 := by
    apply cubicThetaResidueProductReduction_injective hab
    rw [map_mul,map_one,cubicThetaResidueProductReduction_mix,
      cubicThetaResidueProductReduction_mix]
    apply Prod.ext
    · exact inverse_square_product _ _ ht hx
    · exact inverse_square_product _ _ hu hy
  have hunit := (cubicThetaResidueMix_isUnit ha hb hab x y).mpr ⟨hx,hy⟩
  calc
    _ = Ring.inverse (residueMix a b (x,y))*(residueMix a b (x,y)*residueMix a b
        ((Ring.inverse (Ideal.Quotient.mk (modulus a) b))^2*Ring.inverse x,
          (Ring.inverse (Ideal.Quotient.mk (modulus b) a))^2*Ring.inverse y)) := by rw [hm,mul_one]
    _ = _ := by rw [←mul_assoc,Ring.inverse_mul_cancel _ hunit,one_mul]

theorem cubicThetaKloostermanPhase_mix {a b : Eisenstein} (ha : a≠0) (hb : b≠0)
    (hab : IsCoprime a b) (h k : Eisenstein) (x : Residues a) (y : Residues b)
    (hx : IsUnit x) (hy : IsUnit y) :
    residueFourierChar (a*b) (mul_ne_zero ha hb)
      (Ideal.Quotient.mk (modulus (a*b)) h*residueMix a b (x,y)+
        Ideal.Quotient.mk (modulus (a*b)) k*Ring.inverse (residueMix a b (x,y)))=
      residueFourierChar a ha (Ideal.Quotient.mk (modulus a) h*x+
        (Ideal.Quotient.mk (modulus a) k*(Ring.inverse (Ideal.Quotient.mk (modulus a) b))^2)*
          Ring.inverse x)*
      residueFourierChar b hb (Ideal.Quotient.mk (modulus b) h*y+
        (Ideal.Quotient.mk (modulus b) k*(Ring.inverse (Ideal.Quotient.mk (modulus b) a))^2)*
          Ring.inverse y) := by
  rw [AddChar.map_add_eq_mul,cubicThetaResidueMix_inverse ha hb hab x y hx hy,
    residueFourierChar_mix ha hb h,residueFourierChar_mix ha hb k]
  simp only [AddChar.map_add_eq_mul,mul_assoc]
  ring

end CubicFirstMoment

end

end OAI
