import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexSemigroup

namespace OAI

/-! # Strong continuity of the complexified physical evolution

This section of the joint continuity theorem keeps its proof independent of
any concrete matched profile or shooting parameters.
-/

open scoped NNReal

namespace DefocusingNLS

theorem stronglyContinuous_homogeneousComplexLinearizedStep
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (m : ℕ) (q : HomogeneousY a k) (u : HomogeneousY a k × HomogeneousY a k) :
    Continuous (fun t : ℝ≥0 =>
      homogeneousComplexLinearizedStep a b k ha ha1 hk m q t u) := by
  exact (continuous_homogeneousComplexLinearizedStep_apply a b k ha ha1 hk m q).curry_left

end DefocusingNLS

end OAI
