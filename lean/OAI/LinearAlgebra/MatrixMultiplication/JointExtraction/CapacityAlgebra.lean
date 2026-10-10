import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.EntropyMax

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

namespace MatrixMultiplication.JointCapacityAlgebra

open scoped BigOperators

theorem total_sub_max_degrees (A X Y Z : ℝ) :
    A - max (A - X) (max (A - Y) (A - Z)) = min X (min Y Z) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem weighted_joint_capacity {H : Type*} [Fintype H]
    (mass entropy : H → ℝ) (capacity : H → Fin 3 → ℝ) :
    (∑ h, mass h * entropy h) -
        max (∑ h, mass h * (entropy h - capacity h 0))
          (max (∑ h, mass h * (entropy h - capacity h 1))
            (∑ h, mass h * (entropy h - capacity h 2))) =
      min (∑ h, mass h * capacity h 0)
        (min (∑ h, mass h * capacity h 1) (∑ h, mass h * capacity h 2)) := by
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  exact total_sub_max_degrees _ _ _ _

end MatrixMultiplication.JointCapacityAlgebra

end OAI
