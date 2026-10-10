import OAI.Probability.InvariantIsing.Core.ReferenceInfiniteReplicas
import OAI.Probability.InvariantIsing.Arrays.CoordinatePairData

namespace OAI

/-! The manuscript's finite two-replica tensor average in the actual infinite replica law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem tensorTiltedPairPathMean_eq_integral {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ)
    (Φ : ℕ × (Fin n → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) → ℝ)
    (hΦ : Measurable Φ) {C : ℝ} (hB : ∀ p, |Φ p| ≤ C) :
    tensorTiltedPairPathMean eig U c I degree amplitude n b v z Φ =
      ∫ q : TensorCoordinateData I degree n × (ℕ → LabeledLeaf n),
        Φ (coordinatePairData n (q.1.2,q.2))
        ∂(tensorCoordinateLaw I degree n b v ⊗ₘ
          probabilityReplicaKernel (tensorLabeledTerminalGibbs eig U c I degree amplitude n z)
            (measurable_tensorLabeledTerminalGibbs eig U c I degree amplitude n z)) := by
  have hG : Measurable (fun q : TensorCoordinateData I degree n × (ℕ → LabeledLeaf n) =>
      Φ (coordinatePairData n (q.1.2,q.2))) :=
    hΦ.comp ((measurable_coordinatePairData n).comp (measurable_fst.snd.prodMk measurable_snd))
  have hiG : Integrable (fun q : TensorCoordinateData I degree n × (ℕ → LabeledLeaf n) =>
      Φ (coordinatePairData n (q.1.2,q.2)))
      (tensorCoordinateLaw I degree n b v ⊗ₘ
        probabilityReplicaKernel (tensorLabeledTerminalGibbs eig U c I degree amplitude n z)
          (measurable_tensorLabeledTerminalGibbs eig U c I degree amplitude n z)) :=
    Integrable.of_bound hG.aestronglyMeasurable C (ae_of_all _ fun q => by
      simpa only [Real.norm_eq_abs] using hB _)
  rw [Measure.integral_compProd hiG]
  apply integral_congr_ae
  filter_upwards [tensorLabeledTerminal_exp_integrable_ae hN eig U c I degree amplitude n b v hb z] with p hp
  exact referenceReplicaMean_infinite (labeledLeafLaw n p.1)
    (fun α => spinTensorTerminal eig U c I degree amplitude
      (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) α z)) hp
    (fun σ : Fin 2 → LabeledLeaf n => Φ
      (labeledCommonDepth n (σ 0) (σ 1),fun i => (p.2 (edgeAt n (σ 0) i),p.2 (edgeAt n (σ 1) i))))
    (measurable_of_countable _)

end InvariantIsing

end

end OAI
