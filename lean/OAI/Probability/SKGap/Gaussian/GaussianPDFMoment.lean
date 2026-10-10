import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussMoment

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKGapCutoff.Clock

lemma gaussianPDF_moment (v : ℝ≥0) (y x : ℝ) :
    gaussianPDFReal y v x = (Real.sqrt (2*Real.pi*v))⁻¹ *
      gaussMoment (1/(2*(v:ℝ))) 0 (x-y) := by
  unfold gaussianPDFReal gaussMoment
  simp only [pow_zero,one_mul]
  congr 2
  ring

theorem finite_gaussianPDF_approximation {v w : ℝ≥0} (hv : 0 < v) (hw : 0 < w)
    (hwv : w ≤ v) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℝ) (c : ℝ → ℝ),
      (∫ x : ℝ, |gaussianPDFReal 0 w x-
        ∑ y ∈ s, c y*gaussianPDFReal (-y) v x|) < ε := by
  have hvR : (0:ℝ) < v := hv
  have hwR : (0:ℝ) < w := hw
  let kv : ℝ := (Real.sqrt (2*Real.pi*v))⁻¹
  let kw : ℝ := (Real.sqrt (2*Real.pi*w))⁻¹
  have hkv : 0 < kv := by dsimp [kv]; positivity
  have hkw : 0 < kw := by dsimp [kw]; positivity
  have hra : 0 < 1/(2*(v:ℝ)) := by positivity
  have hrab : 1/(2*(v:ℝ)) ≤ 1/(2*(w:ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (show (w:ℝ) ≤ v from hwv) (by norm_num)
  obtain ⟨s,c,hc⟩ := finite_gaussian_approximation hra hrab (show 0 < ε/kw by positivity)
  refine ⟨s,fun y => kw*c y/kv,?_⟩
  have he (x : ℝ) : |gaussianPDFReal 0 w x-
      ∑ y ∈ s, (kw*c y/kv)*gaussianPDFReal (-y) v x| =
      kw*|gaussMoment (1/(2*(w:ℝ))) 0 x-
        ∑ y ∈ s, c y*gaussMoment (1/(2*(v:ℝ))) 0 (x+y)| := by
    simp only [gaussianPDF_moment,sub_zero,sub_neg_eq_add]
    change |kw*gaussMoment (1/(2*(w:ℝ))) 0 x-
      ∑ y ∈ s, (kw*c y/kv)*(kv*gaussMoment (1/(2*(v:ℝ))) 0 (x+y))| = _
    have hterm (y : ℝ) : (kw*c y/kv)*(kv*gaussMoment (1/(2*(v:ℝ))) 0 (x+y)) =
        kw*(c y*gaussMoment (1/(2*(v:ℝ))) 0 (x+y)) := by field_simp
    simp_rw [hterm]
    rw [← Finset.mul_sum,← mul_sub,abs_mul,abs_of_pos hkw]
  simp_rw [he]
  rw [integral_const_mul]
  have hh := mul_lt_mul_of_pos_left hc hkw
  rwa [mul_div_cancel₀ _ hkw.ne'] at hh

end SKGapCutoff.Clock

open MeasureTheory Filter
open scoped Topology

end

end OAI
