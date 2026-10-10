import OAI.Analysis.Laughlin.ThreeBody.HighestEigen

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem threeGram_transpose (Q : ℕ) : (threeGram Q)ᵀ = threeGram Q := by
  ext a b
  simp only [Matrix.transpose_apply,threeGram_entry]
  have hd : (if b=a then (1 : ℝ) else 0) = (if a=b then 1 else 0) := by
    by_cases h : a=b
    · simp [h]
    · simp [h,Ne.symm h]
  rw [hd]
  congr 2
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem threeGram_lowering (Q : ℕ) (hQ : 0 < Q) :
    threeGram Q * (totalRaise (2*Q-2) Q)ᵀ = (totalRaise (2*Q-2) Q)ᵀ * threeGram Q := by
  have h := congrArg Matrix.transpose (threeGram_raising Q hQ)
  simpa only [Matrix.transpose_mul,threeGram_transpose] using h.symm

noncomputable def coupledDescendant (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (n : ℕ) :
    PairOrbitalIndex Q → ℝ :=
  ((totalRaise (2*Q-2) Q)ᵀ ^ n) *ᵥ coupledHighest Q z hQ hz

theorem coupledDescendant_succ (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (n : ℕ) :
    coupledDescendant Q z hQ hz (n+1) =
      (totalRaise (2*Q-2) Q)ᵀ *ᵥ coupledDescendant Q z hQ hz n := by
  simp only [coupledDescendant,pow_succ',Matrix.mulVec_mulVec]

theorem threeGram_descendant_eigen (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (n : ℕ) :
    threeGram Q *ᵥ coupledDescendant Q z hQ hz n =
      (1+gramEigenvalueFormula Q z) • coupledDescendant Q z hQ hz n := by
  induction n with
  | zero => simpa [coupledDescendant] using threeGram_highest_eigen Q z hQ hz
  | succ n ih =>
    rw [coupledDescendant_succ,Matrix.mulVec_mulVec,threeGram_lowering Q (by omega),
      ← Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul]

theorem threeGram_sub_one_descendant_eigen (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (n : ℕ) :
    (threeGram Q-1) *ᵥ coupledDescendant Q z hQ hz n =
      gramEigenvalueFormula Q z • coupledDescendant Q z hQ hz n := by
  rw [Matrix.sub_mulVec,threeGram_descendant_eigen,Matrix.one_mulVec]
  funext i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

end Laughlin.Spin

end OAI
