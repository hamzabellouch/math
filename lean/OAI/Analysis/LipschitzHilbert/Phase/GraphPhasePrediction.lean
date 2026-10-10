import OAI.Analysis.LipschitzHilbert.Phase.GraphPhaseAverage
import OAI.Analysis.LipschitzHilbert.Trees.HierarchyNormalization

namespace OAI

/-!
# The mass-normalized node prediction

The explicitly constructed graph selection law and the diagonal Fourier gain
bound the original parent/child ratio from §8, after the exact normalization
identity. This is the normalized prediction estimate used in §9.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

omit [Fintype ι] [Fintype κ] in
theorem diagonalModulation_smul (frequency : κ → ℝ) (a : EuclideanSpace ℂ κ)
    (c : ℂ) (t : ℝ) : diagonalModulation frequency (c • a) t =
      c • diagonalModulation frequency a t := by
  apply PiLp.ext
  intro j
  simp only [diagonalModulation, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
  ring

omit [Fintype κ] in
theorem diagonalFourierSum_coefficients (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (c : ι → ℂ) (t : ℝ) :
    diagonalFourierSum frequency (fun i => c i • a i) t =
      ∑ i, c i • diagonalModulation (frequency i) (a i) t := by
  rw [diagonalFourierSum_eq_sum]
  simp only [diagonalModulation_smul]

/-- The exact pointwise node/child normalization after diagonal modulation. -/
theorem diagonal_normalized_child_ratio (frequency : ι → κ → ℝ)
    (n : ℝ) (m : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (lambda : ι → ℂ)
    (μ α p t : ℝ) (hn : 0 < n) (hm : ∀ i, 0 < m i) (hrelation : p * μ = α - 1) :
    (n + n ^ (α - p) * ‖diagonalFourierSum frequency (fun i => lambda i • A i) t‖ ^ p) /
      (n + ∑ i, m i ^ (α - p) * ‖A i‖ ^ p) =
    (1 + ‖diagonalFourierSum frequency
      (fun i => ((((m i / n) ^ (1 - μ) : ℝ) : ℂ) * lambda i) •
        (((m i ^ (μ - 1) : ℝ) : ℂ) • A i)) t‖ ^ p) /
      (1 + ∑ i, (m i / n) * ‖((m i ^ (μ - 1) : ℝ) : ℂ) • A i‖ ^ p) := by
  have h := normalized_child_ratio n m (fun i => diagonalModulation (frequency i) (A i) t)
    lambda μ α p hn hm hrelation
  have hleft : (∑ i, lambda i • diagonalModulation (frequency i) (A i) t) =
      diagonalFourierSum frequency (fun i => lambda i • A i) t :=
    (diagonalFourierSum_coefficients frequency A lambda t).symm
  have hright : (∑ i, ((((m i / n) ^ (1 - μ) : ℝ) : ℂ) * lambda i) •
      (((m i ^ (μ - 1) : ℝ) : ℂ) • diagonalModulation (frequency i) (A i) t)) =
      diagonalFourierSum frequency
      (fun i => ((((m i / n) ^ (1 - μ) : ℝ) : ℂ) * lambda i) •
        (((m i ^ (μ - 1) : ℝ) : ℂ) • A i)) t := by
    rw [diagonalFourierSum_coefficients]
    simp only [diagonalModulation_smul]
  rw [hleft, hright] at h
  simpa only [norm_diagonalModulation, ← diagonalModulation_smul] using h

/-- The graph assumptions and original child masses imply the actual ratio
average is at most one, with no selection-law hypothesis. -/
theorem graph_node_prediction_average
    (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w m : ι → ℝ) (n : ℝ) (hw : ∀ i, 0 < w i) (hn : 0 < n)
    (hm : ∀ i, orderMass w (closedNeighborhood G i) ≤ m i)
    (hchildren : ∑ i, w i ≤ n)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (frequency : ι → κ → ℝ)
    (A : ι → EuclideanSpace ℂ κ) (lambda : ι → ℂ)
    {gap D p α : ℝ} (hgap : 0 < gap) (hν : FourierGap ν gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hrelation : p * phaseMu D p = α - 1)
    (hfrequency : ∀ i j, i ≠ j → ¬G i j → ∀ k, gap ≤ |frequency i k - frequency j k|)
    (hcard : ∀ S : Finset ι, (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card : ℝ) ≤ D)
    (hlambda : ∀ i, ‖lambda i‖ ≤ (w i / m i) ^ phaseMu D p) :
    (∫ t, (n + n ^ (α - p) *
      ‖diagonalFourierSum frequency (fun i => lambda i • A i) t‖ ^ p) /
      (n + ∑ i, w i ^ (α - p) * ‖A i‖ ^ p) ∂ν) ≤ 1 := by
  have htotal : ∑ i, w i / n ≤ 1 := by
    rw [← Finset.sum_div]
    exact (div_le_one hn).2 hchildren
  have h := graph_weighted_diagonal_prediction_average G hG w m hw hm ν frequency
    (fun i => w i / n) (fun i => ((w i ^ (phaseMu D p - 1) : ℝ) : ℂ) • A i) lambda
    hgap hν hD hp hfrequency hcard (fun i => div_nonneg (hw i).le hn.le) htotal hlambda
  have heq (t : ℝ) := diagonal_normalized_child_ratio frequency n w A lambda
    (phaseMu D p) α p t hn hw hrelation
  simpa only [← heq] using h

end LipschitzHilbert

end

end OAI
