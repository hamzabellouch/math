import OAI.Probability.InvariantIsing.Fields.CascadeSeedPath

namespace OAI

/-! A pair of ancestor-generated paths on the independent uniform forest. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

def seedForestPairData (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ)) (z : ι → ℝ)
    (q : (ℕ → LabeledLeaf n) × MarkForest unitInterval n) :
    ℕ × (Fin n → (ι → ℝ) × (ι → ℝ)) :=
  (labeledCommonDepth n (q.1 0) (q.1 1),fun i =>
    (cascadeSeedPath n ψ z q.2 (q.1 0) i,cascadeSeedPath n ψ z q.2 (q.1 1) i))

lemma measurable_seedForestPairData (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z : ι → ℝ) :
    Measurable (seedForestPairData n ψ z) := by
  have hm : Measurable (fun p : LabeledLeaf n × MarkForest unitInterval n =>
      cascadeSeedPath n ψ z p.2 p.1) := by
    apply measurable_from_prod_countable_right
    intro α
    exact (measurable_cascadeSeedPath n ψ hψ α).comp (measurable_const.prodMk measurable_id)
  change Measurable (fun q : (ℕ → LabeledLeaf n) × MarkForest unitInterval n =>
    (labeledCommonDepth n (q.1 0) (q.1 1),fun i =>
      (cascadeSeedPath n ψ z q.2 (q.1 0) i,cascadeSeedPath n ψ z q.2 (q.1 1) i)))
  apply Measurable.prodMk
  · have hp : Measurable (fun q : (ℕ → LabeledLeaf n) × MarkForest unitInterval n =>
        (q.1 0,q.1 1)) :=
      ((measurable_pi_apply 0).comp measurable_fst).prodMk
        ((measurable_pi_apply 1).comp measurable_fst)
    exact (measurable_of_countable (fun p : LabeledLeaf n × LabeledLeaf n =>
      labeledCommonDepth n p.1 p.2)).comp hp
  · have hp (j : ℕ) : Measurable (fun q : (ℕ → LabeledLeaf n) × MarkForest unitInterval n =>
        (q.1 j,q.2)) :=
      ((measurable_pi_apply j).comp measurable_fst).prodMk measurable_snd
    exact Measurable.of_eval fun i =>
      ((measurable_pi_apply i).comp (hm.comp (hp 0))).prodMk
      ((measurable_pi_apply i).comp (hm.comp (hp 1)))

end InvariantIsing

end

end OAI
