import OAI.Geometry.NodalSets.Elliptic.SeedLogNonvanishing
import OAI.Geometry.NodalSets.Elliptic.SeedLogSecondDerivative

namespace OAI

namespace Yau.Target
open scoped ContDiff RealInnerProductSpace
noncomputable section

def seedRealGradient : SeedAmbient := WithLp.toLp 2 ![7/3,0,1/6,0,-4/3]
def seedImagGradient : SeedAmbient := WithLp.toLp 2 ![0,3,0,3/2,0]

lemma seedLogReal_first_at_point (v : SeedAmbient) :
    fderiv ℝ seedLogReal (seedPoint : SeedAmbient) v = 3*v 0 + (3/2)*v 2 := by
  rw [(seedLogReal_hasFDerivAt seedPoint_mem_logDomain).fderiv]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,
    smul_eq_mul,seedPoint_quadratic,seedQuadraticDerivative,add_apply,
    seedPoint_z1,seedPoint_z2]
  norm_num [seedZ1_apply,seedZ2_apply,div_eq_mul_inv,Complex.mul_re,Complex.mul_im]
  simp
  ring

lemma seedLogImag_first_at_point (v : SeedAmbient) :
    fderiv ℝ seedLogImag (seedPoint : SeedAmbient) v = 3*v 1 + (3/2)*v 3 := by
  rw [(seedLogImag_hasFDerivAt seedPoint_mem_logDomain).fderiv]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,
    smul_eq_mul,seedPoint_quadratic,seedQuadraticDerivative,add_apply,
    seedPoint_z1,seedPoint_z2]
  norm_num [seedZ1_apply,seedZ2_apply,div_eq_mul_inv,Complex.mul_re,Complex.mul_im]
  simp
  ring

lemma seedLogReal_second_at_point (v w : SeedAmbient) :
    fderiv ℝ (fderiv ℝ seedLogReal) (seedPoint : SeedAmbient) w v =
      -9*v 0*w 0 + 9*v 1*w 1 - (9/4)*v 2*w 2 + (9/4)*v 3*w 3 := by
  rw [seedLogReal_second seedPoint_mem_logDomain]
  simp only [smul_apply,
    smul_eq_mul,seedPoint_quadratic,seedQuadraticDerivative,add_apply,
    seedPoint_z1,seedPoint_z2]
  norm_num [seedZ1_apply,seedZ2_apply,div_eq_mul_inv,Complex.mul_re,Complex.mul_im]
  simp
  ring

lemma seedRealGradient_tangent : ⟪(seedPoint : SeedAmbient),seedRealGradient⟫ = (0:ℝ) := by
  rw [PiLp.inner_apply]
  norm_num [seedPoint,seedPointVector,seedRealGradient,Fin.sum_univ_succ,Matrix.cons_val_succ]

lemma seedImagGradient_tangent : ⟪(seedPoint : SeedAmbient),seedImagGradient⟫ = (0:ℝ) := by
  rw [PiLp.inner_apply]
  norm_num [seedPoint,seedPointVector,seedImagGradient,Fin.sum_univ_succ,Matrix.cons_val_succ]

lemma seedRealGradient_pair (v : SeedAmbient)
    (hv : ⟪(seedPoint : SeedAmbient),v⟫ = (0:ℝ)) :
    ⟪seedRealGradient,v⟫ = fderiv ℝ seedLogReal (seedPoint : SeedAmbient) v := by
  rw [seedLogReal_first_at_point,PiLp.inner_apply]
  rw [PiLp.inner_apply] at hv
  simp [seedPoint,seedPointVector,Fin.sum_univ_succ,Matrix.cons_val_succ] at hv
  simp [seedRealGradient,Fin.sum_univ_succ,Matrix.cons_val_succ]
  linarith

lemma seedImagGradient_pair (v : SeedAmbient) :
    ⟪seedImagGradient,v⟫ = fderiv ℝ seedLogImag (seedPoint : SeedAmbient) v := by
  rw [seedLogImag_first_at_point,PiLp.inner_apply]
  simp [seedImagGradient,Fin.sum_univ_succ,Matrix.cons_val_succ]
  ring

lemma seedGradient_geometry :
    ⟪seedRealGradient,seedRealGradient⟫ = (29/4:ℝ) ∧
    ⟪seedImagGradient,seedImagGradient⟫ = (45/4:ℝ) ∧
    ⟪seedRealGradient,seedImagGradient⟫ = (0:ℝ) ∧
    ⟪seedRealGradient,seedImagTestVector⟫ = (0:ℝ) ∧
    ⟪seedImagTestVector,seedImagTestVector⟫ = (1:ℝ) := by
  simp only [PiLp.inner_apply]
  norm_num [seedRealGradient,seedImagGradient,seedImagTestVector,
    Fin.sum_univ_succ,Matrix.cons_val_succ]

end
end Yau.Target

end OAI
