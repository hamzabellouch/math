import OAI.Probability.InvariantIsing.Fields.CascadeSeedPath
import OAI.Probability.InvariantIsing.Fields.NoiseLeafAncestry

namespace OAI

/-! The joint branch-depth and two-mark-path observable on noise replicas. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def noiseReplicaPairData {A : Type} (n : ℕ) (σ : ℕ → NoiseLeaf A n) :
    ℕ × (Fin n → A × A) :=
  (noiseLeafCommonDepth n (σ 0) (σ 1),fun i => (noiseLeafMark n (σ 0) i,noiseLeafMark n (σ 1) i))

lemma measurable_noiseReplicaPairData {A : Type} [MeasurableSpace A] (n : ℕ) :
    Measurable (noiseReplicaPairData (A := A) n) := by
  change Measurable (fun σ : ℕ → NoiseLeaf A n =>
    (noiseLeafCommonDepth n (σ 0) (σ 1),
      fun i => (noiseLeafMark n (σ 0) i,noiseLeafMark n (σ 1) i)))
  apply Measurable.prodMk
  · have hp : Measurable (fun σ : ℕ → NoiseLeaf A n => (σ 0,σ 1)) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    exact (measurable_noiseLeafCommonDepth (A := A) (B := A) n).comp hp
  · exact Measurable.of_eval fun i =>
      ((measurable_noiseLeafMark n i).comp (measurable_pi_apply 0)).prodMk
        ((measurable_noiseLeafMark n i).comp (measurable_pi_apply 1))

lemma noiseReplicaPairData_keep_labeled {A S : Type} [MeasurableSpace A]
    (n : ℕ) (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S) (s : S)
    (T : LabeledTree n) (g : ForestVertex n → A) (σ : ℕ → LabeledLeaf n)
    (hdepth : noiseLeafCommonDepth n
      (noiseLeafKeep n c u s (labeledNoiseLeaf A n (T,markForestOfCoords A n g) (σ 0)))
      (noiseLeafKeep n c u s (labeledNoiseLeaf A n (T,markForestOfCoords A n g) (σ 1))) =
        labeledCommonDepth n (σ 0) (σ 1)) :
    noiseReplicaPairData n (fun i => noiseLeafKeep n c u s
      (labeledNoiseLeaf A n (T,markForestOfCoords A n g) (σ i))) =
      (labeledCommonDepth n (σ 0) (σ 1),fun i => (g (edgeAt n (σ 0) i),g (edgeAt n (σ 1) i))) := by
  apply Prod.ext hdepth
  funext i
  simp only [noiseReplicaPairData,noiseLeafMark_keep,noiseLeafMark_labeled]

end InvariantIsing

end

end OAI
