import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspRowMajorant
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingRows

namespace OAI

/-! Actual primitive bottom rows transported into an arbitrary integral
cusp. The row map remains injective and preserves the literal height. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaCuspRow (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow) : CubicThetaPrimitiveRow :=
  cubicThetaPrimitiveRow (r.completion.val*δ)

lemma cubicThetaCuspRow_coordinates (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow) :
    (cubicThetaCuspRow δ r).c=r.c*δ 0 0+r.d*δ 1 0 ∧
    (cubicThetaCuspRow δ r).d=r.c*δ 0 1+r.d*δ 1 1 := by
  have hc := congrArg CubicThetaBottomRow.c r.completion_row
  have hd := congrArg CubicThetaBottomRow.d r.completion_row
  change r.completion.val 1 0=r.c at hc
  change r.completion.val 1 1=r.d at hd
  simp only [cubicThetaCuspRow,cubicThetaPrimitiveRow,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two,hc,hd]
  exact ⟨trivial,trivial⟩

lemma cubicThetaCuspRow_injective (δ : SL(2,Eisenstein)) :
    Function.Injective (cubicThetaCuspRow δ) := by
  intro r t h
  have hu : IsUnit (δ.val) := (Group.isUnit δ).map Matrix.SpecialLinearGroup.coeMonoidHom
  have hv : ![r.c,r.d] ᵥ* δ.val=![t.c,t.d] ᵥ* δ.val := by
    apply funext
    intro j
    fin_cases j
    · simpa [Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.head_cons,Matrix.head_fin_const] using
        ((cubicThetaCuspRow_coordinates δ r).1.symm.trans
          ((congrArg CubicThetaPrimitiveRow.c h).trans (cubicThetaCuspRow_coordinates δ t).1))
    · simpa [Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.head_cons,Matrix.head_fin_const] using
        ((cubicThetaCuspRow_coordinates δ r).2.symm.trans
          ((congrArg CubicThetaPrimitiveRow.d h).trans (cubicThetaCuspRow_coordinates δ t).2))
  have he := Matrix.vecMul_injective_of_isUnit hu hv
  exact CubicThetaBottomRow.ext (congrFun he 0) (congrFun he 1)

lemma cubicThetaCuspRow_height (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    (cubicThetaCuspRow δ r).height p=
      r.height (cubicThetaMobius (cubicThetaFullComplex δ) p) := by
  rw [cubicThetaCuspRow,cubicThetaPrimitiveRow_height,map_mul,← cubicThetaMobius_comp _ _ hp]
  have he : cubicThetaFullComplex r.completion.val=cubicThetaPrincipalComplex r.completion := rfl
  rw [he,← cubicThetaBottomRow_height,r.completion_row]

lemma cubicThetaCuspRow_height_zero_c {r : CubicThetaPrimitiveRow} (hc : r.c=0)
    (p : ℂ × ℝ) : r.height p=p.2 := by
  have hu : IsUnit r.d := isCoprime_zero_left.mp (hc ▸ r.coprime)
  simp only [CubicThetaPrimitiveRow.height,CubicThetaPrimitiveRow.denominator,hc,
    ZeroMemClass.coe_zero,zero_mul,zero_add,norm,Complex.normSq_zero]
  rw [show Complex.normSq (r.d:ℂ)=1 from norm_of_isUnit hu,add_zero,div_one]

end CubicFirstMoment

end

end OAI
