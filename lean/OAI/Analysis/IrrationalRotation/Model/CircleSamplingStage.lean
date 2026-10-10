import OAI.Analysis.IrrationalRotation.Model.TrialSampling
import OAI.Analysis.IrrationalRotation.Model.StrictPhase

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Invariant233

structure CircleSamplingStage (θ : ℝ) (j K d q₀ m : ℕ) (R : ℝ) where
  q : ℕ → ℕ
  samples : Fin q₀ → Finset ℕ
  q_zero : q 0 = q₀
  q_pos : ∀ i, 0 < q i
  q_strict : StrictMono q
  q_div : ∀ i, q i ∣ q (i + 1)
  q_ratio : ∀ i < m, R ≤ (q (i + 1) : ℝ) / q i
  phases : ∀ i : Fin m,
    Int.fract ((q (i.val + 1) : ℝ) * θ) ∈
      Ioo (1 / ((m : ℝ) * K)) (2 / ((m : ℝ) * K))
  spread : ProductPhases.strictLargePhaseCondition Finset.univ ((m : ℝ) * K)
    (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
  samples_nonempty : ∀ r, (samples r).Nonempty
  samples_positive : ∀ r, ∀ n ∈ samples r, 0 < n
  samples_range : ∀ r, ∀ n ∈ samples r,
    (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n ∧
      (n : ℝ) ≤ (m : ℝ) ^ ((7 / 10 : ℝ) * m)
  samples_phase : ∀ r, ∀ n ∈ samples r,
    Int.fract ((n : ℝ) * θ - (r.val : ℝ) / q₀) ∈
      Ioo 0 (1 / (((j + 1 : ℕ) : ℝ) ^ 2 * (1 + (d : ℝ)) * q₀))
  sampling_L2 : ∀ r endpoint,
    eLpNorm (fun x : Circle => TrialSampling.average m (samples r) endpoint
      (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
      (fun i : Fin m => (q (i.val + 1) : ℤ) • x) - 1) 2 circleMeasure <
        ENNReal.ofReal (1 / (j : ℝ))

end Invariant233

namespace Invariant233

def CircleStageSupply (θ : ℝ) : Prop :=
  ∀ j K d q₀ : ℕ, 0 < j → 0 < K → 0 < q₀ →
    ∀ᶠ m : ℕ in Filter.atTop, ∀ R : ℝ,
      Nonempty (CircleSamplingStage θ j K d q₀ m R)

end Invariant233

end

end OAI
