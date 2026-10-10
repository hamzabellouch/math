import OAI.Probability.InvariantIsing.Arrays.TensorMinimumIncrement
import OAI.Probability.InvariantIsing.Cavity.CavityTensorPressureMean

namespace OAI

/-! The true minimizing pressure envelopes dominate the original physical
full-minus-base cavity increment, up to explicit vanishing penalty terms. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_minimum_increment {N n m depth : ℕ} (hN : 0<N)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν]
    (eigF : Fin (N+n) → ℝ) (eigB : Fin N → ℝ)
    (IF : Fin m → Finset (Fin (N+n))) (IB : Fin m → Finset (Fin N))
    (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (uF : Fin (N+n) → ℝ) (vF : Fin m → ℝ) (uB : Fin N → ℝ) (vB : Fin m → ℝ)
    (huB : ∀ j, uB j ∈ Set.Icc (1 : ℝ) 2) (hvB : ∀ a, vB a ∈ Set.Icc (1 : ℝ) 2)
    (hminF : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (cavityOrientedBaseLaw (by omega) μ) eigF (fun _ => 0) IF
        1 depth b (fun _ => 0) uF vF ≤
      tensorPerturbationObjective (cavityOrientedBaseLaw (by omega) μ) eigF (fun _ => 0) IF
        1 depth b (fun _ => 0) u' v') :
    let OF := tensorPerturbationObjective (cavityOrientedBaseLaw (by omega) μ) eigF (fun _ => 0) IF
      1 depth b (fun _ => 0) uF vF
    let OB := tensorPerturbationObjective (cavityOrientedBaseLaw hN ν) eigB (fun _ => 0) IB
      1 depth b (fun _ => 0) uB vB
    let θ : Measure (LabeledTree depth) := labeledCascadeLaw depth b;
    -(N+n : ℝ)*OF+(N : ℝ)*OB ≥
      ((∫ p, cavityRotationLogMean p.2 (diagonalPerturbedEigenvalues eigF IF vB 1) IF
          (cavityBaseAmplitude uB) p.1 ∂μ.prod θ) -
       (∫ p, cavityRotationLogMean p.2 (diagonalPerturbedEigenvalues eigB IB vB 1) IB
          (cavityBaseAmplitude uB) p.1 ∂ν.prod θ)) -
      (n : ℝ)*tensorMinimumPenalty uB vB - (N+n : ℝ)*(1/4:ℝ)*(1/2:ℝ)^N := by
  intro OF OB θ
  have hh := tensor_minimum_increment (depth := depth) (cavityOrientedBaseLaw (by omega) μ)
    (cavityOrientedBaseLaw hN ν) eigF (fun _ => 0) eigB (fun _ => 0) IF IB
    1 b (fun _ => 0) uF vF uB vB huB hvB hminF
  have hfull := cavity_tensor_pressure_mean (by omega : 0<N+n) μ eigF IF
    (cavityBaseAmplitude uB) vB 1 b hb
  have hbase := cavity_tensor_pressure_mean hN ν eigB IB (cavityBaseAmplitude uB) vB 1 b hb
  rw [cavityBaseAmplitude_restrict] at hbase
  dsimp only at hh
  simp only [Nat.cast_add] at hfull
  rw [← hfull, ← hbase] at hh
  exact hh

end InvariantIsing

end

end OAI
