import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperSuccessEvent
import OAI.Combinatorics.ContingencyTables.Transport.UniformPartialRejection
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperOuterBudget
import OAI.Combinatorics.ContingencyTables.Transport.ReferenceDrawBounds

namespace OAI

/-! # The actual stationary outer rejection law and its polynomial trial budget -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

/-- Read balance and padding, then return the unique unpadded table. -/
abbrev stateTrial : PaperStateJoint r c → Option (Table r c) :=
  partialEquivDraw (StateJointSuccess r c) (originalStateSuccessEquiv r c)

theorem stationary_trial_mass [Nonempty (PaperStates r c)] [Nonempty (Table r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20)) (X : Table r c) :
    successMass (stationaryJointLaw r c i₀ j₀) (stateTrial r c) X=
      1/(Fintype.card (PaperStateJoint r c):ℚ) := by
  rw [stationaryJointLaw_uniform]
  exact partialEquiv_success_mass _ _ X

/-- No approximate draw is conditioned on success. Ideal complete trials
have fallback error exactly bounded by their geometric failure tail. -/
theorem ideal_outer_variation [Nonempty (PaperStates r c)] [Nonempty (Table r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (htotal : ∑ i,r i=∑ j,c j) (fallback : Table r c) (n : ℕ) :
    (variation (retryLaw (stationaryJointLaw r c i₀ j₀) (stateTrial r c) fallback n)
      (uniformLaw (α := Table r c)):ℝ) ≤
      Real.exp (-(n:ℝ)/(2*(1+(dimensionAllowance (I := I) (J := J):ℝ)^2))) := by
  rw [stationaryJointLaw_uniform]
  apply uniform_partial_retry_exp (StateJointSuccess r c) (originalStateSuccessEquiv r c)
    fallback n (2*(1+(dimensionAllowance (I := I) (J := J):ℝ)^2))
  rw [paperStateJoint_card]
  exact stationary_success_ratio r c htotal (reference_dimension_fourteen r c _ i₀ j₀)

end
end ContingencyTables.SmallGraphProfiles

end OAI
