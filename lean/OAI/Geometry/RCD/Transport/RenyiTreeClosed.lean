import OAI.Geometry.RCD.Transport.CanonicalRenyiConstruction

namespace OAI

/-! # Closed finite constraints for the fixed midpoint tree -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [SeparableSpace X] [CompleteSpace X] in
theorem isClosed_evaluation_measure_eq (ν : Measure X) (hν : IsProbabilityMeasure ν) (t : Time) :
    IsClosed {π : ProbabilityMeasure C(Time,X) | (π:Measure C(Time,X)).map (fun γ => γ t)=ν} := by
  let v : ProbabilityMeasure X := ⟨ν,hν⟩
  have hc := isClosed_eq (ProbabilityMeasure.continuous_map (continuous_eval_const t))
    (continuous_const : Continuous (fun _ : ProbabilityMeasure C(Time,X) => v))
  convert hc using 1
  ext π
  constructor
  · intro h
    apply ProbabilityMeasure.toMeasure_injective
    exact h
  · intro h
    exact congrArg (fun v : ProbabilityMeasure X => (v:Measure X)) h

theorem isClosed_followsRenyiTree {n : ℕ} {K q : ℝ}
    (S : ∀ a : RenyiTransportNode n X, RenyiNodeSplit K q a) (m : ℕ) :
    ∀ (a : RenyiTransportNode n X) (f : Time → Time),
    IsClosed {π : ProbabilityMeasure C(Time,X) |
      FollowsRenyiTree S a (fun t => (π:Measure C(Time,X)).map (fun γ => γ (f t))) m} := by
  induction m with
  | zero =>
    intro a f
    exact (isClosed_evaluation_measure_eq a.left a.left_probability (f 0)).inter
      (isClosed_evaluation_measure_eq a.right a.right_probability (f 1))
  | succ m ih =>
    intro a f
    let := (S a).probability
    exact (isClosed_evaluation_measure_eq a.left a.left_probability (f 0)).inter
      ((isClosed_evaluation_measure_eq a.right a.right_probability (f 1)).inter
      ((isClosed_evaluation_measure_eq ((S a).plan.map (fun γ : C(Time,X) => γ midpointTime))
        inferInstance (f midpointTime)).inter
      ((ih (S a).leftNode (fun t => f (lowerTime t))).inter
        (ih (S a).rightNode (fun t => f (upperTime t))))))

theorem FollowsRenyiTree.of_le {n : ℕ} {K q : ℝ}
    {S : ∀ a : RenyiTransportNode n X, RenyiNodeSplit K q a}
    {a : RenyiTransportNode n X} {ν : Time → Measure X} {k m : ℕ}
    (h : FollowsRenyiTree S a ν m) (hkm : k ≤ m) : FollowsRenyiTree S a ν k := by
  have hm : Antitone (fun j => {ν : Time → Measure X | FollowsRenyiTree S a ν j}) :=
    antitone_nat_of_succ_le (fun j ν hν => hν.of_succ)
  exact hm hkm h

end RegularPointCoordinates

end

end OAI
