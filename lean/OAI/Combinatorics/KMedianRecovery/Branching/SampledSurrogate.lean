import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.DyadicExponent
import OAI.Combinatorics.KMedianRecovery.Recovery.Score

namespace OAI

namespace MetricKMedianRecovery.Completion
open Categorical FiniteSampling

variable {E P R : Type*} [Fintype E] [DecidableEq E] [Fintype P] [Fintype R]

noncomputable def sampledSurrogate {a : ℕ} (part : E → Fin a)
    (hp : Function.Surjective part) (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ) (epsilon : ℝ)
    (bits : BinaryOracleIndex E a (stepExponent a epsilon)
      (sampleCount (Fintype.card E) a epsilon) → Bool) : Finset E :=
  sampledCategorical part hp (saving K q base distance weight redBase redDistance) epsilon bits

lemma sampledSurrogate_feasible {a : ℕ} (part : E → Fin a)
    (hp : Function.Surjective part) (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ) (epsilon : ℝ)
    (bits : BinaryOracleIndex E a (stepExponent a epsilon)
      (sampleCount (Fintype.card E) a epsilon) → Bool) :
    PartitionFeasible part
      (sampledSurrogate part hp K q base distance weight redBase redDistance epsilon bits) :=
  sampledCategorical_feasible part hp _ epsilon bits

lemma sampledSurrogate_expected {a : ℕ} (part : E → Fin a)
    (hp : Function.Surjective part) (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ)
    (hw : ∀ r, 0 ≤ weight r) {theta : ℝ} (ht : 1/Real.exp 1 < theta)
    (S : Finset E) (hS : PartitionFeasible part S) :
    average (fun bits : BinaryOracleIndex E a (stepExponent a (theta-1/Real.exp 1))
        (sampleCount (Fintype.card E) a (theta-1/Real.exp 1)) → Bool =>
      surrogate K q base distance weight redBase redDistance
        (sampledSurrogate part hp K q base distance weight redBase redDistance
          (theta-1/Real.exp 1) bits)) ≤
      theta * surrogate K q base distance weight redBase redDistance ∅ +
        (1-theta) * surrogate K q base distance weight redBase redDistance S := by
  have hh := sampledCategorical_expected part hp
    (saving K q base distance weight redBase redDistance)
    (saving_mono K q base distance weight redBase redDistance hw)
    (fun X Y hXY e => saving_diminishing K q base distance weight redBase redDistance hw hXY e)
    (saving_empty K q base distance weight redBase redDistance)
    (sub_pos.mpr ht) S hS
  simp only [saving,average_sub,average_const] at hh
  dsimp only [sampledSurrogate]
  nlinarith

end MetricKMedianRecovery.Completion

end OAI
