import OAI.Analysis.Laughlin.FourBody.CopyOperatorHaar

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

def firstOddPairLabel (D : ℕ) (hD : 1 ≤ D) : OddPairLabel D := ⟨0,by omega⟩

theorem fourCopyOperator_diagonal (Q D : ℕ) (hQ : D+2 ≤ Q) (c : OddPairLabel D → ℝ) :
    fourCopyOperator Q D hQ (Matrix.diagonal c) = ∑ r,
      (c r : ℂ) • (retainedFourInclusion Q D hQ r * (retainedFourInclusion Q D hQ r)ᴴ) := by
  classical
  simp [fourCopyOperator,Matrix.diagonal_apply,apply_ite,ite_smul]

theorem fourCopyOperator_sub (Q D : ℕ) (hQ : D+2 ≤ Q)
    (C E : OddPairLabel D → OddPairLabel D → ℝ) :
    fourCopyOperator Q D hQ (C-E) = fourCopyOperator Q D hQ C-fourCopyOperator Q D hQ E := by
  simp only [fourCopyOperator,Pi.sub_apply,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]

theorem fourCopyOperator_middle (Q D : ℕ) (hQ : D+2 ≤ Q) (hD : 1 ≤ D) :
    fourCopyOperator Q D hQ (finiteFourMiddle Q D) =
      (fourDimensionRatio Q D : ℂ) •
        (retainedFourInclusion Q D hQ (firstOddPairLabel D hD) *
          (retainedFourInclusion Q D hQ (firstOddPairLabel D hD))ᴴ) +
      ((3/10^6 : ℝ) : ℂ) • (∑ r : OddPairLabel D,
        retainedFourInclusion Q D hQ r * (retainedFourInclusion Q D hQ r)ᴴ) -
      fourCopyOperator Q D hQ (fun r s => physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s)) := by
  classical
  unfold finiteFourMiddle
  erw [fourCopyOperator_sub,fourCopyOperator_diagonal]
  have he (r : OddPairLabel D) : Certificate.copyLabel r=1 ↔ r=firstOddPairLabel D hD := by
    dsimp [Certificate.copyLabel,firstOddPairLabel]
    constructor
    · intro h; apply Fin.ext; dsimp; omega
    · intro h; have := congrArg Fin.val h; dsimp at this; omega
  simp only [Complex.ofReal_add,add_smul,Finset.sum_add_distrib]
  simp_rw [he]
  simp only [apply_ite,Complex.ofReal_zero,ite_smul,zero_smul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,← Finset.smul_sum]
  rfl

theorem fourDimensionRatio_exact (Q D : ℕ) (hQ : D+2 ≤ Q) :
    fourDimensionRatio Q D =
      ((4*Q-1-2*D : ℕ) : ℝ)/((2*Q-2+1 : ℕ) : ℝ) := by
  unfold fourDimensionRatio
  congr 1
  · rw [Nat.cast_sub (by omega : 2*D ≤ 4*Q-1),Nat.cast_sub (by omega : 1 ≤ 4*Q)]
    push_cast
    ring
  · rw [Nat.cast_add,Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast
    ring

end Laughlin.Fock

end OAI
