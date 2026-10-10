import OAI.Analysis.LipschitzHilbert.Trees.SourceBalancedBlend
import OAI.Analysis.LipschitzHilbert.Phase.GraphPredictionFactor
import OAI.Analysis.LipschitzHilbert.Phase.GraphPhasePrediction

namespace OAI

/-! The source node ratio and its snapshot graph predictor, with the original
child amplitudes and masses kept explicit. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- The exact source prediction in mass-normalized child variables. -/
def sourcePredictionValue (p μ n : ℝ) (c : ι → ℝ)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) : ℝ :=
  energyRatio p (1+∑ i, (c i/n)*‖(c i)^(μ-1) • A i‖^p)
    (∑ i, (((c i/n)^(1-μ):ℝ):ℂ) • (lam i • ((c i)^(μ-1) • A i)))

/-- The same snapshot, with only its prescribed diagonal carriers moving. -/
def sourceSnapshotPrediction (p μ n : ℝ) (c : ι → ℝ)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) (frequency : ι → κ → ℝ) (b : ℝ) : ℝ :=
  energyRatio p (1+∑ i, (c i/n)*‖(c i)^(μ-1) • A i‖^p)
    (∑ i, (((c i/n)^(1-μ):ℝ):ℂ) •
      (lam i • diagonalModulation (frequency i) ((c i)^(μ-1) • A i) b))

theorem source_prediction_numerator_identity {p n μ : ℝ} (hn : 0 < n)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) :
    sourcePredictionValue p μ n c A lam =
      energyRatio p (1+∑ i, (c i/n)*‖(c i)^(μ-1) • A i‖^p)
        (∑ i, ((n^(μ-1):ℝ):ℂ) • (lam i • A i)) := by
  unfold sourcePredictionValue
  congr 1
  exact Finset.sum_congr rfl fun i _ => source_normalized_numerator_eq hn (hc i) μ (lam i) (A i)

/-- The graph averaging theorem applies to exactly the source snapshot. -/
theorem source_snapshot_graph_identity (p D n : ℝ) (c : ι → ℝ)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) (frequency : ι → κ → ℝ) (b : ℝ) :
    sourceSnapshotPrediction p (phaseMu D p) n c A lam frequency b =
      graphPredictionValue frequency (fun i => c i/n)
        (fun i => (c i)^(phaseMu D p-1) • A i) lam D p b := by
  unfold sourceSnapshotPrediction graphPredictionValue predictionCoefficients
  rw [diagonalFourierSum_coefficients]
  simp only [mul_smul]

/-- The coefficient sum used by the line-grid theorem follows from the
original amplitudes and actual child fractions, including after shrinkage. -/
theorem source_snapshot_graph_coefficient_sum {p D n ε C K u : ℝ}
    (hn : 0 < n) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hsize : C*n^(phaseMu D p) ≤ K)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (hA : ∀ i, ‖A i‖ ≤ C*c i) (hlam : ∀ i, ‖lam i‖ ≤ 1)
    (hmass : ∑ i, c i/n ≤ u) :
    (∑ i, ‖predictionCoefficients (fun i => c i/n)
      (fun i => (c i)^(phaseMu D p-1) • radialShrink (2*ε*c i) (A i)) lam D p i‖) ≤ K*u := by
  have hterm (i : ι) : ‖predictionCoefficients (fun i => c i/n)
      (fun i => (c i)^(phaseMu D p-1) • radialShrink (2*ε*c i) (A i)) lam D p i‖ ≤
      K*(c i/n) := by
    unfold predictionCoefficients
    rw [mul_smul,source_normalized_numerator_eq hn (hc i)]
    have ha : ‖radialShrink (2*ε*c i) (A i)‖ ≤ C*c i :=
      (norm_radialShrink_le (mul_nonneg (mul_nonneg (by norm_num) hε) (hc i).le) _).trans (hA i)
    exact (source_numerator_term_bound hn (hc i) hC _ _ ha (hlam i)).trans
      (mul_le_mul_of_nonneg_right hsize (div_pos (hc i) hn).le)
  calc
    _ ≤ ∑ i, K*(c i/n) := Finset.sum_le_sum fun i _ => hterm i
    _ = K*(∑ i, c i/n) := (Finset.mul_sum ..).symm
    _ ≤ K*u := mul_le_mul_of_nonneg_left hmass hK

/-- The shrunken source comparison in the value notation used for assembly. -/
theorem source_balanced_values_blend
    {n n' p μ ε K u C θ : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (hp : 1 ≤ p) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hpower : n^μ ≤ K)
    (hu : 1/2 ≤ u) (hsum : ∑ i, c i/n ≤ 1)
    (frequency : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ) (lam lam' : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (frequency i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ)
    (hnumerator : ∀ i,
      ‖((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)-
        ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
        ε*K*(c i/n))
    (hC : 0 ≤ C) (hsize : C*n^μ ≤ K) (hA : ∀ i, ‖A i‖ ≤ C*c i)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    sourcePredictionValue p μ n' c' A' lam' ≤
      Real.exp ((6*p*ε*K+2*θ*(p*K))*u)*
        ((1-θ)*sourceSnapshotPrediction p μ n c
          (fun i => radialShrink (2*ε*c i) (A i)) lam frequency b+θ) :=
  source_balanced_prediction_blend hn hn' c c' hc hc' hp hε hK hpower hu hsum frequency b
    A A' lam lam' hlam hscaled hnumerator hC hsize hA hθ0 hθ1

end LipschitzHilbert

end

end OAI
