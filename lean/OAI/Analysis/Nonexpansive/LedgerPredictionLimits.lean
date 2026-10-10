import OAI.Analysis.Nonexpansive.PredictionCutoff
import OAI.Analysis.Nonexpansive.BlockEstimates

namespace OAI

/-!
# Actual ideal-cutoff limits for a completed candidate ledger

The coefficient parameter is filled in only after the positive child
weights exist. The exact cutoff identity proves that its prediction limit
is a limit of the actual nonlinear ideal cutoff outputs.
-/

noncomputable section

open Filter
open scoped Topology

namespace ReflexiveFixedPoints.CandidateLedger

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X} {k : ℕ}
variable (L : CandidateLedger T k K) (E : TreeEvaluation W K)

/-- The actual retained parameter inserted into the completed prediction family. -/
def predictionLimit (hK : WeaklyCompact K) (b : ℕ → K) (U : Ultrafilter ℕ)
    (v : T.Node (k + 1)) : K :=
  Prediction.predictionWeakLimit E k (L.earlierParent v) (L.earlierPoint v)
    hK b U (L.actualParameter W v)

/-- The limit comes from already evaluated nonlinear cutoff outputs. -/
theorem tendsto_predictionLimit (hK : WeaklyCompact K)
    (b : ℕ → K) (U : Ultrafilter ℕ) (v : T.Node (k + 1)) :
    Tendsto (fun j => toWeakSpace ℝ X (E.evaluate (k + 1) (L.idealOutput v (b j)) : X))
      (U : Filter ℕ) (𝓝 (toWeakSpace ℝ X (L.predictionLimit E hK b U v : X))) := by
  have h := Prediction.tendsto_predictionWeakLimit E k (L.earlierParent v)
    (L.earlierPoint v) hK b U (L.actualParameter W v)
  simpa only [L.evaluate_idealOutput E, predictionLimit] using h

/-- Once the actual retained labels are identified, the ledger cutoff is
exactly the switching construction's ideal cutoff. -/
theorem idealOutput_eq_idealCutoff (x : K)
    (hlabels : ∀ w, L.retainedPoint w = E.map (k + 1) w x)
    (v : T.Node (k + 1)) (b : K) :
    L.idealOutput v b = E.idealCutoff (k + 1) x b v := by
  funext w
  simp only [idealOutput, TreeEvaluation.idealCutoff, hlabels]

/-- The prediction is an actual weak limit of the ideal cutoff in the
final evaluated tree, with its original maps and weights. -/
theorem tendsto_predictionLimit_idealCutoff (hK : WeaklyCompact K)
    (b : ℕ → K) (U : Ultrafilter ℕ) (x : K)
    (hlabels : ∀ w, L.retainedPoint w = E.map (k + 1) w x)
    (v : T.Node (k + 1)) :
    Tendsto (fun j => toWeakSpace ℝ X
      (E.evaluate (k + 1) (E.idealCutoff (k + 1) x (b j) v) : X))
      (U : Filter ℕ) (𝓝 (toWeakSpace ℝ X (L.predictionLimit E hK b U v : X))) := by
  have h := L.tendsto_predictionLimit E hK b U v
  simpa only [L.idealOutput_eq_idealCutoff E x hlabels] using h

end ReflexiveFixedPoints.CandidateLedger

end

end OAI
