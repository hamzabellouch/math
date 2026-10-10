import OAI.Geometry.RCD.Sobolev.EventualDiagonalLevel
import OAI.Geometry.RCD.Metric.MeasuredApproximation
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Choosing common maps for all fixed-radius measured limits -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem diagonal_measured_approximations {n : ℕ} (μ : Measure X)
    (p : ℕ → X) (r : ℕ → ℝ) (S : ℕ → ℝ)
    (hfinite : ∀ m : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ∃ V : X → Euclidean n, ∀ j ≤ m,
        IsMeasuredEuclideanApproximation μ n (p k) (r k) (S j) η V) :
    ∃ (ε : ℕ → ℝ) (V : ℕ → X → Euclidean n),
      (∀ k, 0 < ε k ∧ ε k ≤ 1) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ j, ∀ᶠ k in atTop,
        IsMeasuredEuclideanApproximation μ n (p k) (r k) (S j) (ε k) (V k) := by
  classical
  let P : ℕ → ℕ → Prop := fun m k => ∃ V : X → Euclidean n, ∀ j ≤ m,
    IsMeasuredEuclideanApproximation μ n (p k) (r k) (S j) (1/((m : ℝ)+1)) V
  obtain ⟨d,hd,hP⟩ := exists_eventual_diagonal_level P
    (fun m => hfinite m (1/((m : ℝ)+1)) (by positivity))
  let ε : ℕ → ℝ := fun k => 1/((d k : ℝ)+1)
  let V : ℕ → X → Euclidean n := fun k => if h : P (d k) k then Classical.choose h else 0
  refine ⟨ε,V,?_,tendsto_one_div_add_atTop_nhds_zero_nat.comp hd,?_⟩
  · intro k
    constructor
    · dsimp only [ε]
      positivity
    · change 1/((d k : ℝ)+1) ≤ 1
      apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) (d k)]
  · intro j
    filter_upwards [hP,hd.eventually (eventually_ge_atTop j)] with k hk hj
    dsimp only [V]
    rw [dite_eq_left hk]
    exact Classical.choose_spec hk j hj

end RegularPointCoordinates

end

end OAI
