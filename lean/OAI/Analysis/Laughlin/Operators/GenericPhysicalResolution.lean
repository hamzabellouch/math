import OAI.Analysis.Laughlin.Spin.Basis2

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem physicalCoupledInclusion_complete (A B : ℕ) :
    (∑ z : Fin (min A B+1),
      physicalCoupledInclusion A B z.val (by omega) (by omega) *
        (physicalCoupledInclusion A B z.val (by omega) (by omega))ᴴ) = 1 := by
  have hc : (genericCoupledBasis A B).map Complex.ofReal *
      ((genericCoupledBasis A B).map Complex.ofReal)ᴴ = 1 := by
    ext i j
    have h := congrArg Complex.ofReal (congrFun (congrFun (genericCoupledBasis_complete A B) i) j)
    simpa only [Matrix.mul_apply,Matrix.map_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply,
      Complex.star_def,Complex.conj_ofReal,Complex.ofReal_sum,Complex.ofReal_mul,Matrix.one_apply,
      apply_ite,Complex.ofReal_one,Complex.ofReal_zero] using h
  rw [← hc]
  ext i j
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.map_apply,
    Fintype.sum_sigma,physicalCoupledInclusion,Matrix.smul_apply,smul_eq_mul,
    genericCoupledInclusion,genericCoupledBasis]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro n hn
  have hp : ((-1 : ℂ)^z.val)*star ((-1 : ℂ)^z.val)=1 := by
    simp only [star_pow,star_neg,star_one,← mul_pow]
    norm_num
  simp only [star_mul]
  calc
    _ = (((-1 : ℂ)^z.val)*star ((-1 : ℂ)^z.val)) *
      ((genericUnitDescendant A B z.val (by omega) (by omega) n.val i : ℂ)*
        star (genericUnitDescendant A B z.val (by omega) (by omega) n.val j : ℂ)) := by ring
    _ = _ := by rw [hp,one_mul]

end Laughlin.Spin

end OAI
