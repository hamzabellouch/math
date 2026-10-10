import OAI.Analysis.LipschitzHilbert.Phase.GraphPredictionFactor
import OAI.Analysis.LipschitzHilbert.Estimates.RadialShrink
import OAI.Analysis.LipschitzHilbert.Phase.ScalarPhase
import OAI.Analysis.LipschitzHilbert.Trees.PathCoefficient

namespace OAI

/-!
# Exact dominant-path coordinates for the graph prediction

The distinguished diagonal carrier and scalar phase are removed explicitly.
The graph prediction then has the path baseline used in §9, with constant
path vector and residual denominator and an oscillating off-path numerator.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

def graphPathVector (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ) (p : ℝ) (i₀ : ι) :
    EuclideanSpace ℂ κ := l i₀ ^ (1 / p) • X i₀

def graphPathCoefficient (l : ι → ℝ) (lambda : ι → ℂ) (D p : ℝ) (i₀ : ι) : ℝ :=
  l i₀ ^ (1 - phaseMu D p - 1 / p) * ‖lambda i₀‖

def graphPathResidual (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ) (p : ℝ) (i₀ : ι) : ℝ :=
  ∑ i : RemainderIndex i₀, l i * ‖X i‖ ^ p

def graphPathOffPath (frequency : ι → κ → ℝ) (l : ι → ℝ)
    (X : ι → EuclideanSpace ℂ κ) (lambda : ι → ℂ) (D p : ℝ) (i₀ : ι) (t : ℝ) :
    EuclideanSpace ℂ κ :=
  (scalarPhase (lambda i₀))⁻¹ • diagonalFourierSum (diagonalRemainderFrequency frequency i₀)
    (fun i : RemainderIndex i₀ => predictionCoefficients l X lambda D p i) t

omit [Fintype ι] [Fintype κ] in
theorem phase_inverse_mul (z : ℂ) (hz : z ≠ 0) : (scalarPhase z)⁻¹ * z = (‖z‖ : ℂ) := by
  rw [scalarPhase_eq_div, inv_div]
  field_simp

omit [Fintype ι] [Fintype κ] in
/-- The path coefficient after its scalar phase has been removed. -/
theorem graph_rotated_path_coefficient (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
    (lambda : ι → ℂ) (D p : ℝ) (i₀ : ι) (hl : 0 < l i₀) (hlambda : lambda i₀ ≠ 0) :
    (scalarPhase (lambda i₀))⁻¹ • predictionCoefficients l X lambda D p i₀ =
      graphPathCoefficient l lambda D p i₀ • graphPathVector l X p i₀ := by
  have hpower : l i₀ ^ (1 - phaseMu D p - 1 / p) * l i₀ ^ (1 / p) =
      l i₀ ^ (1 - phaseMu D p) := by
    rw [← Real.rpow_add hl]
    congr 1
    ring
  have hscalar : graphPathCoefficient l lambda D p i₀ * l i₀ ^ (1 / p) =
      l i₀ ^ (1 - phaseMu D p) * ‖lambda i₀‖ := by
    unfold graphPathCoefficient
    calc
      _ = (l i₀ ^ (1 - phaseMu D p - 1 / p) * l i₀ ^ (1 / p)) * ‖lambda i₀‖ := by ring
      _ = _ := by rw [hpower]
  simp only [predictionCoefficients, graphPathVector,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) hscalar
  push_cast at hcast
  calc
    _ = ((l i₀ ^ (1 - phaseMu D p) : ℝ) : ℂ) *
        ((scalarPhase (lambda i₀))⁻¹ * lambda i₀) := by ring
    _ = _ := by
      rw [phase_inverse_mul _ hlambda, ← hcast]
      rfl

/-- The child denominator splits into path energy and the off-path remainder. -/
theorem graph_path_denominator (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
    {p : ℝ} (hp : 0 < p) (i₀ : ι) (hl : 0 ≤ l i₀) :
    1 + ∑ i, l i * ‖X i‖ ^ p =
      1 + ‖graphPathVector l X p i₀‖ ^ p + graphPathResidual l X p i₀ := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  unfold graphPathVector graphPathResidual
  rw [norm_weighted_smul_rpow hp hl]
  ring

/-- The graph-model prediction is exactly the dominant-path baseline. -/
theorem graph_prediction_path_baseline (frequency : ι → κ → ℝ) (l : ι → ℝ)
    (X : ι → EuclideanSpace ℂ κ) (lambda : ι → ℂ) (D : ℝ) {p : ℝ}
    (hp : 0 < p) (i₀ : ι) (hl : 0 < l i₀) (hlambda : lambda i₀ ≠ 0) (t : ℝ) :
    graphPredictionValue frequency l X lambda D p t =
      energyRatio p (1 + ‖graphPathVector l X p i₀‖ ^ p + graphPathResidual l X p i₀)
        (graphPathCoefficient l lambda D p i₀ • graphPathVector l X p i₀ +
          graphPathOffPath frequency l X lambda D p i₀ t) := by
  unfold graphPredictionValue
  rw [graph_path_denominator l X hp i₀ hl.le,
    diagonal_carrier_energyRatio frequency (predictionCoefficients l X lambda D p) i₀]
  have hunit : ‖(scalarPhase (lambda i₀))⁻¹‖ = 1 := by rw [norm_inv, norm_scalarPhase hlambda, inv_one]
  unfold energyRatio
  congr 2
  congr 1
  calc
    ‖predictionCoefficients l X lambda D p i₀ +
      diagonalFourierSum (diagonalRemainderFrequency frequency i₀)
        (fun i : RemainderIndex i₀ => predictionCoefficients l X lambda D p i) t‖ =
      ‖(scalarPhase (lambda i₀))⁻¹ • (predictionCoefficients l X lambda D p i₀ +
        diagonalFourierSum (diagonalRemainderFrequency frequency i₀)
          (fun i : RemainderIndex i₀ => predictionCoefficients l X lambda D p i) t)‖ := by
      rw [norm_smul, hunit, one_mul]
    _ = _ := by rw [smul_add, graph_rotated_path_coefficient l X lambda D p i₀ hl hlambda]; rfl

theorem graphPathResidual_nonneg (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
    (p : ℝ) (i₀ : ι) (hl : ∀ i, 0 ≤ l i) : 0 ≤ graphPathResidual l X p i₀ := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (Real.rpow_nonneg (norm_nonneg _) _)

/-- The oscillating remainder retains the same off-path coefficient mass. -/
theorem graphPathOffPath_norm_le (frequency : ι → κ → ℝ) (l : ι → ℝ)
    (X : ι → EuclideanSpace ℂ κ) (lambda : ι → ℂ) (D p : ℝ) (i₀ : ι)
    (hlambda : lambda i₀ ≠ 0) (t : ℝ) :
    ‖graphPathOffPath frequency l X lambda D p i₀ t‖ ≤
      ∑ i : RemainderIndex i₀, ‖predictionCoefficients l X lambda D p i‖ := by
  unfold graphPathOffPath
  rw [norm_smul, norm_inv, norm_scalarPhase hlambda, inv_one, one_mul]
  exact diagonalFourierSum_bound _ _ t

omit [Fintype ι] in
/-- The coefficient is the real mass-fraction expression from the source
when the modulus of the hierarchy weight is the expected power. -/
theorem graphPathCoefficient_eq_pathCoefficient (l : ι → ℝ) (lambda : ι → ℂ)
    (D p α r : ℝ) (i₀ : ι) (hp : p ≠ 0) (hrelation : p * phaseMu D p = α - 1)
    (hlambda : ‖lambda i₀‖ = r ^ phaseMu D p) :
    graphPathCoefficient l lambda D p i₀ =
      pathCoefficient (1 - α / p) (phaseMu D p) (l i₀) r := by
  unfold graphPathCoefficient pathCoefficient
  rw [hlambda]
  have hexp : 1 - phaseMu D p - 1 / p = 1 - α / p := by
    field_simp
    nlinarith
  rw [hexp]

end LipschitzHilbert

end

end OAI
