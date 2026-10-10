import Mathlib
import OAI.Analysis.FreeWords.FlipBasic

namespace OAI

noncomputable section

namespace KKFreeLiftDiagnostic

open scoped BigOperators Matrix.Norms.L2Operator Kronecker

noncomputable section

def leftAverage {d : ℕ} (A : Block d) : Block d :=
  (d : ℂ)⁻¹ • ∑ i : Fin d, ∑ j : Fin d,
    left (Matrix.single i j 1)*A*left (Matrix.single j i 1)

theorem left_single_mul {d : ℕ} (i j : Fin d) (A : Block d)
    (k l : Fin d × Fin d) :
    (left (Matrix.single i j 1)*A) k l = if k.1=i then A (j,k.2) l else 0 := by
  classical
  simp only [Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  by_cases hk : k.1=i
  · simp [left,Matrix.kroneckerMap_apply,Matrix.single_apply,Matrix.one_apply,hk]
  · simp [left,Matrix.kroneckerMap_apply,Matrix.one_apply,hk,Ne.symm hk]

theorem mul_left_single {d : ℕ} (i j : Fin d) (A : Block d)
    (k l : Fin d × Fin d) :
    (A*left (Matrix.single i j 1)) k l = if l.1=j then A k (i,l.2) else 0 := by
  classical
  simp only [Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  by_cases hl : l.1=j
  · simp [left,Matrix.kroneckerMap_apply,Matrix.single_apply,Matrix.one_apply,hl]
  · simp [left,Matrix.kroneckerMap_apply,Matrix.one_apply,hl,Ne.symm hl]

theorem leftAverage_eq_partialTrace {d : ℕ} (A : Block d) :
    leftAverage A=right (partialTrace A) := by
  classical
  ext k l
  simp only [leftAverage,Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,
    mul_left_single,left_single_mul]
  by_cases hkl : k.1=l.1
  · simp [right,partialTrace,Matrix.one_apply,hkl]
  · simp [right,partialTrace,hkl]

theorem leftAverage_centeredFlip {d : ℕ} (hd : 0 < d) :
    leftAverage (centeredFlip d)=0 := by
  rw [leftAverage_eq_partialTrace,partialTrace_centeredFlip hd]
  ext i j
  simp [right]

end

end KKFreeLiftDiagnostic
end

end OAI
