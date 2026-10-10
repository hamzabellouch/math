import OAI.Geometry.HeilbronnTriangle.ActualWeightedFiberCount

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

namespace Problem355.ActualPointLaw

open Parameters

def tripleConstant : ℝ :=
  (128 / 7 : ℝ) * UniformFixedFiberCount.countConstant

theorem tripleConstant_nonneg : 0 ≤ tripleConstant :=
  mul_nonneg (by norm_num) UniformFixedFiberCount.countConstant_nonneg

theorem tripleProbability_le {r : ℕ} [Fact r.Prime]
    (D : PrimeParameterData heilbronnK r) :
    (pointLaw D).tripleProbability (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
      tripleConstant * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
        ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) := by
  let : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
  exact tripleProbability_le_of_count D UniformFixedFiberCount.countConstant_nonneg
    (fun A => weightedFiberBound_of_matrix_count _
      UniformFixedFiberCount.matrix_fiber_le D A)

end Problem355.ActualPointLaw

end

end OAI
