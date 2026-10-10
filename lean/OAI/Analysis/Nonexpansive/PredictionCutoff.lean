import OAI.Analysis.Nonexpansive.CandidateLedger
import OAI.Analysis.Nonexpansive.PredictionOutputs

namespace OAI

/-!
# The actual retained coefficient parameter predicts the ideal cutoff

Earlier retained children carry their labels. The current and all later
children carry one common point. Discarded candidates remain in the earlier
parameter domain with zero coefficient. The identity is proved before
applying the identical nonlinear maps on both sides.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints.CandidateLedger

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X} {k : ℕ}
variable (L : CandidateLedger T k K)

/-- The actual coefficients are used only after the retained weights are known. -/
def actualParameter (W : WeightedTree T) (v : T.Node (k + 1)) :
    Prediction.coefficientSet (L.earlierParent v) :=
  ⟨L.actualTheta W v, L.actualTheta_mem W v⟩

/-- The ideal cutoff immediately after the current descendant block switches. -/
def idealOutput (v : T.Node (k + 1)) (b : K) (w : T.Node (k + 1)) : K :=
  if w < v then L.retainedPoint w else b

/-- The actual ideal child average equals its residual candidate prediction. -/
theorem childAverage_idealOutput (E : TreeEvaluation W K)
    (v : T.Node (k + 1)) (b : K) (p : T.Node k) :
    E.childAverage k (L.idealOutput v b) p =
      Prediction.residualInput E k (L.earlierParent v) (L.earlierPoint v)
        b (L.actualParameter W v) p := by
  apply Subtype.ext
  rw [E.childAverage_val, Prediction.residualInput_val]
  change (∑ w ∈ Finset.univ.filter (fun w => T.parent k w = p),
      W.weight k w • (L.idealOutput v b w : X)) = _
  have hideal (w : T.Node (k + 1)) :
      (L.idealOutput v b w : X) =
        if w < v then (L.retainedPoint w : X) else (b : X) := by
    unfold idealOutput
    split_ifs <;> rfl
  simp_rw [hideal]
  exact L.ideal_child_average_eq_residualPoint W v (fun z : K => (z : X)) b p

/-- The ideal cutoff's root output is the already specified prediction,
with actual coefficients inserted only after all weights are fixed. -/
theorem evaluate_idealOutput (E : TreeEvaluation W K)
    (v : T.Node (k + 1)) (b : K) :
    E.evaluate (k + 1) (L.idealOutput v b) =
      Prediction.evaluatedPrediction E k (L.earlierParent v) (L.earlierPoint v)
        b (L.actualParameter W v) := by
  rw [E.evaluate_succ]
  unfold Prediction.evaluatedPrediction
  congr 1
  funext p
  unfold TreeEvaluation.collapse
  rw [L.childAverage_idealOutput E v b p]

end ReflexiveFixedPoints.CandidateLedger

end

end OAI
