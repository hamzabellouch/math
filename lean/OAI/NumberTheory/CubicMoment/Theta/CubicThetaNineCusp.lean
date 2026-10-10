import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAdaptedCusp

namespace OAI

/-! A prescribed first column with lower-right entry divisible by nine.
This makes the common-lattice additive phase a literal residue character. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicTheta_coprime_nine {r : Eisenstein} (hr : primary r) : IsCoprime r 9 := by
  convert (primary_coprime_three hr).pow_right (n:=2) using 1
  norm_num

def cubicThetaInverseNine (r : Eisenstein) (hr : primary r) : Eisenstein :=
  Classical.choose (cubicTheta_coprime_nine hr)

lemma cubicThetaInverseNine_spec (r : Eisenstein) (hr : primary r) :
    (9:Eisenstein)∣1-r*cubicThetaInverseNine r hr := by
  obtain ⟨y,hy⟩ := Classical.choose_spec (cubicTheta_coprime_nine hr)
  refine ⟨y,?_⟩
  change 1-r*Classical.choose (cubicTheta_coprime_nine hr)=9*y
  linear_combination -hy

def cubicThetaNineGaussMatrix (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) : SL(2,Eisenstein) :=
  let g := cubicThetaGaussCuspMatrix r hr u hu
  g*cubicThetaFullTranslation (-(cubicThetaInverseNine r hr*g 1 1))

lemma cubicThetaNineGaussMatrix_entries (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicThetaNineGaussMatrix r hr u hu 0 0=lambdaE^3*u ∧
    cubicThetaNineGaussMatrix r hr u hu 1 0=r ∧
    cubicThetaNineGaussMatrix r hr u hu 1 1=
      cubicThetaGaussCuspMatrix r hr u hu 1 1*(1-r*cubicThetaInverseNine r hr) := by
  let g := cubicThetaGaussCuspMatrix r hr u hu
  change (g.val*(!![1,-(cubicThetaInverseNine r hr*g 1 1);0,1] :
    Matrix (Fin 2) (Fin 2) Eisenstein)) 0 0=_ ∧
    (g.val*!![1,-(cubicThetaInverseNine r hr*g 1 1);0,1]) 1 0=_ ∧
    (g.val*!![1,-(cubicThetaInverseNine r hr*g 1 1);0,1]) 1 1=_
  simp only [Matrix.mul_apply,Fin.sum_univ_two]
  dsimp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  simp only [mul_one,mul_zero,add_zero]
  refine ⟨rfl,rfl,?_⟩
  change r*(-(cubicThetaInverseNine r hr*g 1 1))+g 1 1=_
  ring

lemma cubicThetaNineGaussMatrix_nine (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    (9:Eisenstein)∣cubicThetaNineGaussMatrix r hr u hu 1 1 := by
  rw [(cubicThetaNineGaussMatrix_entries r hr u hu).2.2]
  exact dvd_mul_of_dvd_right (cubicThetaInverseNine_spec r hr) _

lemma cubicThetaNineGaussMatrix_primary (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    primary (cubicThetaNineGaussMatrix r hr u hu 1 0) := by
  rw [(cubicThetaNineGaussMatrix_entries r hr u hu).2.1]
  exact hr

theorem cubicThetaNineGaussMatrix_multiplier (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) (j : Fin 3) :
    cubicThetaProjectedCuspMultiplier (cubicThetaNineGaussMatrix r hr u hu)
      (cubicThetaNineGaussMatrix_primary r hr u hu) j=cubicSymbol r u := by
  let g := cubicThetaNineGaussMatrix r hr u hu
  have hc := cubicThetaNineGaussMatrix_primary r hr u hu
  have hd : (3:Eisenstein)∣g 1 1 :=
    dvd_trans (show (3:Eisenstein)∣9 from ⟨3,by norm_num⟩) (cubicThetaNineGaussMatrix_nine r hr u hu)
  have ha : (3:Eisenstein)∣g 0 0 := by
    rw [(cubicThetaNineGaussMatrix_entries r hr u hu).1]
    refine ⟨-lambdaE*u,?_⟩
    rw [pow_succ,lambdaE_sq]
    ring
  rw [cubicThetaProjectedCuspMultiplier_constant g hc hd j,
    cubicThetaPrimaryBottom_multiplier_adapted g hc ha hd,
    (cubicThetaNineGaussMatrix_entries r hr u hu).2.1,
    (cubicThetaNineGaussMatrix_entries r hr u hu).1,
    cubicSymbol_mul_upper hr,cubicSymbol_pow_upper hr,
    cubicSymbol_cube_of_isCoprime hr lambdaE (primary_coprime_lambda hr),one_mul]

end CubicFirstMoment

end

end OAI
