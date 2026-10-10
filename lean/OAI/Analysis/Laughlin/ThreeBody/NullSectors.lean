import OAI.Analysis.Laughlin.ThreeBody.NullFormula
import OAI.Analysis.Laughlin.ThreeBody.PhysicalKernel
import OAI.Analysis.Laughlin.ThreeBody.SpinProjectors

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

noncomputable def complexThreeSpinProjector (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    Matrix (Spin.PairOrbitalIndex Q) (Spin.PairOrbitalIndex Q) ℂ :=
  fun a b => (Spin.threeSpinProjector Q hQ z a b : ℂ)

theorem complexThreeSpinProjector_eigen (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    complexThreeGram Q * complexThreeSpinProjector Q hQ z =
      ((1+gramEigenvalueFormula Q z.val : ℝ) : ℂ) • complexThreeSpinProjector Q hQ z := by
  ext a b
  have he := congrArg (fun M : Matrix (Spin.PairOrbitalIndex Q) (Spin.PairOrbitalIndex Q) ℝ =>
    (M a b : ℂ)) (Spin.threeSpinProjector_eigen Q hQ z)
  simp only [Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul] at he ⊢
  push_cast at he
  simpa only [complexThreeGram,complexThreeSpinProjector,Complex.ofReal_add,Complex.ofReal_one] using he

theorem source_threeBody_null_sectors (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (hz : z.val=0 ∨ z.val=1 ∨ z.val=3) (u : Spin.PairOrbitalIndex Q → ℂ) :
    threeWedge Q (complexThreeSpinProjector Q hQ z *ᵥ u) = 0 := by
  have hval : gramEigenvalueFormula Q z.val = -1 := by
    rcases hz with hz | hz | hz
    · rw [hz,gramEigenvalueFormula_zero]
    · rw [hz,gramEigenvalueFormula_one Q hQ]
    · rw [hz,gramEigenvalueFormula_three Q (by omega)]
  apply threeWedge_zero_of_gram_zero Q hQ
  rw [Matrix.mulVec_mulVec,complexThreeSpinProjector_eigen,hval]
  simp

end Laughlin.Fock

end OAI
