import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSiegelReduction

namespace OAI

/-! The right action of the full integral modular group on primitive rows.
This transports the positive scalar cutoff into a fixed Siegel set. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def CubicThetaPrimitiveRow.completion (r : CubicThetaPrimitiveRow) : SL(2,Eisenstein) :=
  Classical.choose (cubicThetaPrimitiveRow_surjective r)

lemma CubicThetaPrimitiveRow.completion_row (r : CubicThetaPrimitiveRow) :
    cubicThetaPrimitiveRow r.completion=r := Classical.choose_spec (cubicThetaPrimitiveRow_surjective r)

lemma CubicThetaPrimitiveRow.completion_c (r : CubicThetaPrimitiveRow) :
    r.completion 1 0=r.c := congrArg CubicThetaPrimitiveRow.c r.completion_row

lemma CubicThetaPrimitiveRow.completion_d (r : CubicThetaPrimitiveRow) :
    r.completion 1 1=r.d := congrArg CubicThetaPrimitiveRow.d r.completion_row

def CubicThetaPrimitiveRow.rightMul (r : CubicThetaPrimitiveRow) (g : SL(2,Eisenstein)) :
    CubicThetaPrimitiveRow := cubicThetaPrimitiveRow (r.completion*g)

lemma CubicThetaPrimitiveRow.rightMul_c (r : CubicThetaPrimitiveRow) (g : SL(2,Eisenstein)) :
    (r.rightMul g).c=r.c*g 0 0+r.d*g 1 0 := by
  change (r.completion*g) 1 0=_
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
    r.completion_c,r.completion_d]

lemma CubicThetaPrimitiveRow.rightMul_d (r : CubicThetaPrimitiveRow) (g : SL(2,Eisenstein)) :
    (r.rightMul g).d=r.c*g 0 1+r.d*g 1 1 := by
  change (r.completion*g) 1 1=_
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
    r.completion_c,r.completion_d]

lemma cubicThetaPrimitiveRow_mul (g h : SL(2,Eisenstein)) :
    cubicThetaPrimitiveRow (g*h)=(cubicThetaPrimitiveRow g).rightMul h := by
  apply CubicThetaPrimitiveRow.ext
  · rw [CubicThetaPrimitiveRow.rightMul_c]
    change (g*h) 1 0=g 1 0*h 0 0+g 1 1*h 1 0
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  · rw [CubicThetaPrimitiveRow.rightMul_d]
    change (g*h) 1 1=g 1 0*h 0 1+g 1 1*h 1 1
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]

lemma CubicThetaPrimitiveRow.rightMul_one (r : CubicThetaPrimitiveRow) : r.rightMul 1=r := by
  simp only [CubicThetaPrimitiveRow.rightMul,mul_one,r.completion_row]

lemma CubicThetaPrimitiveRow.rightMul_assoc (r : CubicThetaPrimitiveRow)
    (g h : SL(2,Eisenstein)) : (r.rightMul g).rightMul h=r.rightMul (g*h) := by
  change (cubicThetaPrimitiveRow (r.completion*g)).rightMul h=_
  rw [←cubicThetaPrimitiveRow_mul,mul_assoc,cubicThetaPrimitiveRow_mul,r.completion_row]

def CubicThetaPrimitiveRow.rightMulEquiv (g : SL(2,Eisenstein)) :
    CubicThetaPrimitiveRow ≃ CubicThetaPrimitiveRow where
  toFun r := r.rightMul g
  invFun r := r.rightMul g⁻¹
  left_inv r := by
    change (r.rightMul g).rightMul g⁻¹=r
    rw [r.rightMul_assoc,mul_inv_cancel,r.rightMul_one]
  right_inv r := by
    change (r.rightMul g⁻¹).rightMul g=r
    rw [r.rightMul_assoc,inv_mul_cancel,r.rightMul_one]

lemma CubicThetaPrimitiveRow.height_rightMul (r : CubicThetaPrimitiveRow)
    (g : SL(2,Eisenstein)) {p : ℂ × ℝ} (hp : 0<p.2) :
    (r.rightMul g).height p=r.height (cubicThetaMobius (cubicThetaFullComplex g) p) := by
  rw [CubicThetaPrimitiveRow.rightMul,cubicThetaPrimitiveRow_height,map_mul,
    ←cubicThetaMobius_comp _ _ hp,←cubicThetaPrimitiveRow_height,r.completion_row]

end CubicFirstMoment

end

end OAI
