import OAI.Probability.InvariantIsing.Arrays.CoordinateReplicaAncestry

namespace OAI

/-! The common prefix of sampled unweighted leaves is their labeled common prefix. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma noiseLeafKeep_one {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (v : NoiseLeaf A n) :
    noiseLeafKeep n (fun _ (_ : PUnit × A) => 1) (fun _ _ => PUnit.unit) PUnit.unit v = v := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    change (1 * v.1,(v.2.1,noiseLeafKeep n _ _ _ v.2.2)) = v
    rw [one_mul,ih]

lemma coordinate_unweighted_depth_ae {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure A) :
    let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi fun a : ForestVertex n => (μ (forestVertexDepth n a) : Measure A))
    ∀ᵐ q ∂P ⊗ₘ probabilityReplicaKernel (fun p => labeledLeafLaw n p.1)
        ((measurable_labeledLeafLaw n).comp measurable_fst),
      noiseLeafCommonDepth n
        (labeledNoiseLeaf A n (q.1.1,markForestOfCoords A n q.1.2) (q.2 0))
        (labeledNoiseLeaf A n (q.1.1,markForestOfCoords A n q.1.2) (q.2 1)) =
      labeledCommonDepth n (q.2 0) (q.2 1) := by
  simpa only [noiseLeafKeep_one] using coordinate_sampled_ancestry_ae n b hb μ
    (fun _ (_ : PUnit × A) => 1) (fun _ _ => PUnit.unit)
    (fun _ => measurable_const) (fun _ => measurable_const) (fun _ _ => one_ne_zero)
    PUnit.unit (fun p => labeledLeafLaw n p.1)
    ((measurable_labeledLeafLaw n).comp measurable_fst) (fun _ => Measure.AbsolutelyContinuous.rfl)

end InvariantIsing

end

end OAI
