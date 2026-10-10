import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRationalCusp
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAdaptedMultiplier

namespace OAI

/-! Choose the additive rational cusp lift with a lower-right entry
zero modulo three, preserving the prescribed first column. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaAdaptedCuspMatrix (g : SL(2,Eisenstein)) : SL(2,Eisenstein) :=
  g*cubicThetaFullTranslation (-g 1 1)

lemma cubicThetaAdaptedCuspMatrix_entries (g : SL(2,Eisenstein)) :
    cubicThetaAdaptedCuspMatrix g 0 0=g 0 0 ∧
    cubicThetaAdaptedCuspMatrix g 1 0=g 1 0 ∧
    cubicThetaAdaptedCuspMatrix g 1 1=g 1 1*(1-g 1 0) := by
  change (g.val*(!![1,-g 1 1;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)) 0 0=_ ∧
    (g.val*!![1,-g 1 1;0,1]) 1 0=_ ∧
    (g.val*!![1,-g 1 1;0,1]) 1 1=_
  simp [Matrix.mul_apply,Fin.sum_univ_two]
  ring

lemma cubicThetaAdaptedCuspMatrix_three (g : SL(2,Eisenstein)) (hc : primary (g 1 0)) :
    (3:Eisenstein)∣cubicThetaAdaptedCuspMatrix g 1 1 := by
  rw [(cubicThetaAdaptedCuspMatrix_entries g).2.2]
  have he : 1-g 1 0= -(g 1 0-1) := by ring
  rw [he]
  exact dvd_mul_of_dvd_right (dvd_neg.mpr hc) _

def cubicThetaAdaptedGaussMatrix (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) : SL(2,Eisenstein) :=
  cubicThetaAdaptedCuspMatrix (cubicThetaGaussCuspMatrix r hr u hu)

lemma cubicThetaAdaptedGaussMatrix_top (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicThetaAdaptedGaussMatrix r hr u hu 0 0=lambdaE^3*u :=
  (cubicThetaAdaptedCuspMatrix_entries _).1

lemma cubicThetaAdaptedGaussMatrix_bottom (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicThetaAdaptedGaussMatrix r hr u hu 1 0=r :=
  (cubicThetaAdaptedCuspMatrix_entries _).2.1

theorem cubicThetaAdaptedGaussMatrix_multiplier (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) (j : Fin 3) :
    cubicThetaProjectedCuspMultiplier (cubicThetaAdaptedGaussMatrix r hr u hu)
      (by rw [cubicThetaAdaptedGaussMatrix_bottom]; exact hr) j=cubicSymbol r u := by
  let g := cubicThetaAdaptedGaussMatrix r hr u hu
  have hc : primary (g 1 0) := by rw [cubicThetaAdaptedGaussMatrix_bottom]; exact hr
  have hd : (3:Eisenstein)∣g 1 1 := cubicThetaAdaptedCuspMatrix_three _ hr
  have ha : (3:Eisenstein)∣g 0 0 := by
    rw [cubicThetaAdaptedGaussMatrix_top]
    refine ⟨-lambdaE*u,?_⟩
    rw [pow_succ,lambdaE_sq]
    ring
  rw [cubicThetaProjectedCuspMultiplier_constant g hc hd j,
    cubicThetaPrimaryBottom_multiplier_adapted g hc ha hd,
    cubicThetaAdaptedGaussMatrix_bottom,cubicThetaAdaptedGaussMatrix_top,
    cubicSymbol_mul_upper hr,cubicSymbol_pow_upper hr,
    cubicSymbol_cube_of_isCoprime hr lambdaE (primary_coprime_lambda hr),one_mul]

end CubicFirstMoment

end

end OAI
