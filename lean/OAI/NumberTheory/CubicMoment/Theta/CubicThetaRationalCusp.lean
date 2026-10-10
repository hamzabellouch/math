import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSelectedTransform

namespace OAI

/-! A literal determinant-one lift of each coprime additive numerator.
The lift keeps its prescribed bottom-left entry, including ramified factors. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimitiveMatrix (r a : Eisenstein) (h : IsCoprime r a) : SL(2,Eisenstein) := by
  let u := Classical.choose h
  let v := Classical.choose (Classical.choose_spec h)
  have he : u*r+v*a=1 := Classical.choose_spec (Classical.choose_spec h)
  refine ⟨!![a,-u;r,v],?_⟩
  simp only [Matrix.det_fin_two,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  linear_combination he

@[simp] lemma cubicThetaPrimitiveMatrix_top (r a : Eisenstein) (h : IsCoprime r a) :
    cubicThetaPrimitiveMatrix r a h 0 0=a := rfl

@[simp] lemma cubicThetaPrimitiveMatrix_bottom (r a : Eisenstein) (h : IsCoprime r a) :
    cubicThetaPrimitiveMatrix r a h 1 0=r := rfl

lemma cubicThetaPrimitiveMatrix_cusp (r a : Eisenstein) (h : IsCoprime r a) :
    cubicThetaPrimaryCuspCenter (cubicThetaPrimitiveMatrix r a h)=(a:ℂ)/(r:ℂ) := rfl

/-- Lambda cubed cancels the selected frequency denominator. -/
def cubicThetaGaussCuspMatrix (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) : SL(2,Eisenstein) :=
  cubicThetaPrimitiveMatrix r (lambdaE^3*u) (((primary_coprime_lambda hr).pow_right).mul_right hu)

@[simp] lemma cubicThetaGaussCuspMatrix_bottom (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicThetaGaussCuspMatrix r hr u hu 1 0=r := rfl

lemma cubicThetaGaussCuspMatrix_cusp (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicThetaPrimaryCuspCenter (cubicThetaGaussCuspMatrix r hr u hu)=
      (traceLambda^3*(u:ℂ))/(r:ℂ) := by
  change ((lambdaE^3*u:Eisenstein):ℂ)/(r:ℂ)=_
  rw [Subalgebra.coe_mul,Subalgebra.coe_pow,lambdaE_coe]

end CubicFirstMoment

end

end OAI
