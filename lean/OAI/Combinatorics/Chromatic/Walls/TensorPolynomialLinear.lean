import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.TensorPolynomialBox

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
open scoped TensorProduct
variable {A B α β : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]

noncomputable def boxRightLinear (p : MvPolynomial α A) :
    MvPolynomial β B →ₗ[ℚ] MvPolynomial (α⊕β) (A⊗[ℚ]B) :=
  { toFun := box p
    map_add' := by intro q r; simp only [box,map_add,mul_add]
    map_smul' := by
      intro r q
      ext z
      rw [←Finsupp.comapDomain_sumElim_comapDomain z,coeff_box,coeff_smul,coeff_smul,coeff_box]
      exact (TensorProduct.mk ℚ A B _).map_smul r _ }

noncomputable def boxLeftLinear (q : MvPolynomial β B) :
    MvPolynomial α A →ₗ[ℚ] MvPolynomial (α⊕β) (A⊗[ℚ]B) :=
  { toFun := fun p=>box p q
    map_add' := by intro p r; simp only [box,map_add,add_mul]
    map_smul' := by
      intro r p
      ext z
      rw [←Finsupp.comapDomain_sumElim_comapDomain z,coeff_box,coeff_smul,coeff_smul,coeff_box]
      rw [←TensorProduct.smul_tmul',RingHom.id_apply] }

end ElementaryPositivity.CenterCalculus

end

end OAI
