import OAI.Combinatorics.Progressions.Polynomial.AllocatedNestedDegreeInduction

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem candidateDetectionLoss_le_retained_mass
    {loss gainLog sourceMassLog factorMassLog mass : ℝ}
    (hloss : loss ≤ Real.exp (-gainLog) / 2)
    (hmass : Real.exp (-sourceMassLog) ≤ mass)
    (hgain : sourceMassLog + factorMassLog ≤ gainLog) :
    loss ≤ (9 / 10 : ℝ) * (Real.exp (-factorMassLog) * mass) := by
  have hproduct : Real.exp (-gainLog) ≤ Real.exp (-factorMassLog) * mass := by
    calc
      Real.exp (-gainLog) ≤ Real.exp (-(sourceMassLog + factorMassLog)) :=
        Real.exp_le_exp.mpr (neg_le_neg hgain)
      _ = Real.exp (-factorMassLog) * Real.exp (-sourceMassLog) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-factorMassLog) * mass :=
        mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _)
  have hnonneg : 0 ≤ Real.exp (-factorMassLog) * mass :=
    (Real.exp_nonneg _).trans hproduct
  apply hloss.trans
  calc
    Real.exp (-gainLog) / 2 ≤ (Real.exp (-factorMassLog) * mass) / 2 :=
      div_le_div_of_nonneg_right hproduct (by norm_num)
    _ ≤ (9 / 10 : ℝ) * (Real.exp (-factorMassLog) * mass) := by linarith

end Erdos3.VectorPolynomial

end

end OAI
