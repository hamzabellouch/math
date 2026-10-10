import OAI.Probability.InvariantIsing.Fields.NoiseReplicaPairData
import OAI.Probability.IsingPerceptron.SamplingIndependent

namespace OAI

/-! The measurable labeled two-path observable in the original forest coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def coordinatePairData {A : Type} (n : ℕ)
    (p : (ForestVertex n → A) × (ℕ → LabeledLeaf n)) : ℕ × (Fin n → A × A) :=
  (labeledCommonDepth n (p.2 0) (p.2 1),
    fun i => (p.1 (edgeAt n (p.2 0) i),p.1 (edgeAt n (p.2 1) i)))

lemma measurable_coordinatePairData {A : Type} [MeasurableSpace A] (n : ℕ) :
    Measurable (coordinatePairData (A := A) n) := by
  have hE : Measurable (fun p : (ForestVertex n → A) × LabeledLeaf n =>
      fun i => p.1 (edgeAt n p.2 i)) := by
    apply measurable_from_prod_countable_left
    intro α
    exact Measurable.of_eval fun i => measurable_pi_apply (edgeAt n α i)
  have hp (j : ℕ) : Measurable (fun p : (ForestVertex n → A) × (ℕ → LabeledLeaf n) =>
      (p.1,p.2 j)) := measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)
  have hd : Measurable (fun p : (ForestVertex n → A) × (ℕ → LabeledLeaf n) =>
      (p.2 0,p.2 1)) := ((measurable_pi_apply 0).comp measurable_snd).prodMk
        ((measurable_pi_apply 1).comp measurable_snd)
  exact ((measurable_of_countable (fun q : LabeledLeaf n × LabeledLeaf n =>
    labeledCommonDepth n q.1 q.2)).comp hd).prodMk (Measurable.of_eval fun i =>
      ((measurable_pi_apply i).comp (hE.comp (hp 0))).prodMk
        ((measurable_pi_apply i).comp (hE.comp (hp 1))))

end InvariantIsing

end

end OAI
