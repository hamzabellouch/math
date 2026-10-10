import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBottomRow

namespace OAI

/-! Choice-independent bottom-row multipliers and the exact right action
used to reindex the cubic Eisenstein series. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def CubicThetaBottomRow.phase (r : CubicThetaBottomRow) : ℂ := star (cubicSymbol r.d r.c)

lemma cubicThetaKubotaValue_bottomRow (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue g = (cubicThetaBottomRow g).phase := by
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubota_column_switch]
  have hd := (cubicThetaPrincipalGroup_diagonal_primary g).2
  have hr := (cubicThetaBottomRow g).coprime.symm
  change IsCoprime (g.val 1 1) (g.val 1 0) at hr
  have he : g.val 1 1 ∣ g.val 0 1*g.val 1 0-(-1) := by
    refine ⟨g.val 0 0,?_⟩
    linear_combination -cubicThetaPrincipalGroup_det g
  have hprod : cubicSymbol (g.val 1 1) (g.val 0 1)*cubicSymbol (g.val 1 1) (g.val 1 0) = 1 := by
    rw [←cubicSymbol_mul_upper hd,cubicSymbol_congr (residue_eq_of_dvd_sub he),
      cubicSymbol_neg hd,cubic_reciprocity hd primary_one,cubicSymbol_one_lower]
  have hn : cubicSymbol (g.val 1 1) (g.val 1 0)*star (cubicSymbol (g.val 1 1) (g.val 1 0)) = 1 := by
    calc
      _ = (‖cubicSymbol (g.val 1 1) (g.val 1 0)‖:ℂ)^2 := Complex.mul_conj' _
      _ = 1 := by rw [norm_cubicSymbol_of_isCoprime hd hr]; norm_num
  change cubicSymbol (g.val 1 1) (g.val 0 1) = star (cubicSymbol (g.val 1 1) (g.val 1 0))
  calc
    _ = cubicSymbol (g.val 1 1) (g.val 0 1)*
        (cubicSymbol (g.val 1 1) (g.val 1 0)*star (cubicSymbol (g.val 1 1) (g.val 1 0))) := by
      rw [hn,mul_one]
    _ = _ := by rw [←mul_assoc,hprod,one_mul]

lemma CubicThetaBottomRow.phase_norm (r : CubicThetaBottomRow) : ‖r.phase‖ = 1 := by
  exact (norm_star _).trans (norm_cubicSymbol_of_isCoprime r.d_primary r.coprime.symm)

def CubicThetaBottomRow.rightMul (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup) :
    CubicThetaBottomRow := cubicThetaBottomRow (r.completion*g)

lemma CubicThetaBottomRow.rightMul_c (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup) :
    (r.rightMul g).c = r.c*g.val 0 0+r.d*g.val 1 0 := by
  have hc := congrArg CubicThetaBottomRow.c r.completion_row
  have hd := congrArg CubicThetaBottomRow.d r.completion_row
  change (r.completion.val*g.val) 1 0 = _
  simpa only [cubicThetaBottomRow,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two] using
    congrArg₂ (fun c d => c*g.val 0 0+d*g.val 1 0) hc hd

lemma CubicThetaBottomRow.rightMul_d (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup) :
    (r.rightMul g).d = r.c*g.val 0 1+r.d*g.val 1 1 := by
  have hc := congrArg CubicThetaBottomRow.c r.completion_row
  have hd := congrArg CubicThetaBottomRow.d r.completion_row
  change (r.completion.val*g.val) 1 1 = _
  simpa only [cubicThetaBottomRow,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two] using
    congrArg₂ (fun c d => c*g.val 0 1+d*g.val 1 1) hc hd

lemma cubicThetaBottomRow_mul (g h : cubicThetaPrincipalGroup) :
    (cubicThetaBottomRow g).rightMul h = cubicThetaBottomRow (g*h) := by
  apply CubicThetaBottomRow.ext
  · rw [CubicThetaBottomRow.rightMul_c]
    change g.val 1 0*h.val 0 0+g.val 1 1*h.val 1 0 = (g.val*h.val) 1 0
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  · rw [CubicThetaBottomRow.rightMul_d]
    change g.val 1 0*h.val 0 1+g.val 1 1*h.val 1 1 = (g.val*h.val) 1 1
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]

@[simp] lemma CubicThetaBottomRow.rightMul_one (r : CubicThetaBottomRow) : r.rightMul 1 = r := by
  change cubicThetaBottomRow (r.completion*1) = r
  rw [mul_one,r.completion_row]

lemma CubicThetaBottomRow.rightMul_mul (r : CubicThetaBottomRow) (g h : cubicThetaPrincipalGroup) :
    (r.rightMul g).rightMul h = r.rightMul (g*h) := by
  change (cubicThetaBottomRow (r.completion*g)).rightMul h = cubicThetaBottomRow (r.completion*(g*h))
  rw [cubicThetaBottomRow_mul,mul_assoc]

def CubicThetaBottomRow.rightMulEquiv (g : cubicThetaPrincipalGroup) :
    CubicThetaBottomRow ≃ CubicThetaBottomRow where
  toFun r := r.rightMul g
  invFun r := r.rightMul g⁻¹
  left_inv r := by
    change (r.rightMul g).rightMul g⁻¹ = r
    rw [rightMul_mul,mul_inv_cancel,rightMul_one]
  right_inv r := by
    change (r.rightMul g⁻¹).rightMul g = r
    rw [rightMul_mul,inv_mul_cancel,rightMul_one]

lemma CubicThetaBottomRow.phase_rightMul (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup) :
    (r.rightMul g).phase = r.phase*cubicThetaKubotaValue g := by
  rw [rightMul,←cubicThetaKubotaValue_bottomRow,cubicThetaKubotaValue_mul,
    cubicThetaKubotaValue_bottomRow,r.completion_row]

end CubicFirstMoment

end

end OAI
