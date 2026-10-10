import OAI.Analysis.Laughlin.FourBody.CopyAlgebra

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem contractionForm_add {I : Type*} [Fintype I] (Q : ℕ)
    (L : I → Module.End ℂ (Space Q)) (M N : Matrix I I ℂ) (x : Space Q) :
    contractionForm Q L (M+N) x = contractionForm Q L M x+contractionForm Q L N x := by
  simp only [contractionForm,Matrix.add_apply,add_mul,Finset.sum_add_distrib]

theorem contractionForm_sub {I : Type*} [Fintype I] (Q : ℕ)
    (L : I → Module.End ℂ (Space Q)) (M N : Matrix I I ℂ) (x : Space Q) :
    contractionForm Q L (M-N) x = contractionForm Q L M x-contractionForm Q L N x := by
  simp only [contractionForm,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

theorem fourCopyMiddleForm (Q D : ℕ) (hQ : D+2 ≤ Q) (hD : 1 ≤ D) (x : Space Q) :
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ (finiteFourMiddle Q D)) x).re =
    (contractionForm Q (sourceFourFamilyEnd Q)
      (retainedFourInclusion Q D hQ (firstOddPairLabel D hD) *
        (retainedFourInclusion Q D hQ (firstOddPairLabel D hD))ᴴ) x).re +
    (3/10^6 : ℝ) * (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (∑ r : OddPairLabel D, (contractionForm Q (sourceFourFamilyEnd Q)
        (retainedFourInclusion Q D hQ r*(retainedFourInclusion Q D hQ r)ᴴ) x).re) -
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (contractionForm Q (sourceFourFamilyEnd Q)
        (fourCopyOperator Q D hQ (fun r s => physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s))) x).re := by
  rw [fourCopyOperator_middle Q D hQ hD,contractionForm_sub,contractionForm_add]
  simp only [contractionForm_smul,contractionForm_sum,Complex.sub_re,Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.re_sum]
  rw [fourDimensionRatio_exact Q D hQ]
  have ha : ((2*Q-2+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd : ((4*Q-1-2*D : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 4*Q-1-2*D ≠ 0 by omega)
  field_simp

end Laughlin.Fock

end OAI
