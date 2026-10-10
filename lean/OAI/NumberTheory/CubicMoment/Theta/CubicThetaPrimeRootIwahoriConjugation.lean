import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootCoverDomain

namespace OAI

/-! The arithmetic Iwahori subgroup normalizes the actual root-cover
subgroup. The proof retains its lower-entry and central-diagonal congruences. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootIwahori_lower (g h : cubicThetaPrincipalGroup) :
    (g*h*g⁻¹).val 1 0=
      g.val 1 0*g.val 1 1*(h.val 0 0-h.val 1 1)+
        (g.val 1 1)^2*h.val 1 0-(g.val 1 0)^2*h.val 0 1 := by
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

lemma cubicThetaPrimeRootIwahori_diagonal (g h : cubicThetaPrincipalGroup) :
    (g*h*g⁻¹).val 0 0-(g*h*g⁻¹).val 1 1=
      (g.val 0 0*g.val 1 1+g.val 0 1*g.val 1 0)*(h.val 0 0-h.val 1 1)+
        2*g.val 0 1*g.val 1 1*h.val 1 0-2*g.val 0 0*g.val 1 0*h.val 0 1 := by
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

def cubicThetaPrimeRootIwahoriConjugate {p : Eisenstein} (g : cubicThetaPrimeIwahori p)
    (h : cubicThetaPrimeRootSubgroup p) : cubicThetaPrimeRootSubgroup p :=
  ⟨g.val*h.val*g.val⁻¹,by
    obtain ⟨C,hC⟩ := g.property
    obtain ⟨c,hc⟩ := h.property.1
    obtain ⟨d,hd⟩ := h.property.2
    change p^2∣(g.val*h.val*g.val⁻¹).val 1 0 ∧
      p∣(g.val*h.val*g.val⁻¹).val 0 0-(g.val*h.val*g.val⁻¹).val 1 1
    rw [cubicThetaPrimeRootIwahori_lower,cubicThetaPrimeRootIwahori_diagonal,hC,hc,hd]
    constructor
    · refine ⟨C*g.val.val 1 1*d+(g.val.val 1 1)^2*c-C^2*h.val.val 0 1,?_⟩
      ring
    · refine ⟨(g.val.val 0 0*g.val.val 1 1+g.val.val 0 1*(p*C))*d+
        2*g.val.val 0 1*g.val.val 1 1*p*c-2*g.val.val 0 0*C*h.val.val 0 1,?_⟩
      ring⟩

def cubicThetaPrimeRootIwahoriEquiv {p : Eisenstein} (g : cubicThetaPrimeIwahori p) :
    cubicThetaPrimeRootSubgroup p ≃ cubicThetaPrimeRootSubgroup p where
  toFun := cubicThetaPrimeRootIwahoriConjugate g
  invFun := cubicThetaPrimeRootIwahoriConjugate g⁻¹
  left_inv h := by
    apply Subtype.ext
    change g.val⁻¹*(g.val*h.val*g.val⁻¹)*(g.val⁻¹)⁻¹=h.val
    group
  right_inv h := by
    apply Subtype.ext
    change g.val*(g.val⁻¹*h.val*(g.val⁻¹)⁻¹)*g.val⁻¹=h.val
    group

end CubicFirstMoment

end

end OAI
