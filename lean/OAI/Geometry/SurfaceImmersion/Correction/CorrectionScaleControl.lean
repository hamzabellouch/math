import OAI.Geometry.SurfaceImmersion.Correction.CorrectionScales

namespace OAI

/-! Positivity and the cumulative displacement budget for the actual scales. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace ClosedSurfaceR4.ExactCorrection

lemma correctionScale_pos {t : ℝ} (ht : 0 < t) (n : ℕ) :
    0 < correctionScale t n := by
  induction n with
  | zero => exact ht
  | succ n hn => exact Real.rpow_pos_of_pos hn _

lemma correctionScale_le_initial {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1/32) (n : ℕ) :
    correctionScale t n ≤ t := by
  apply (correctionScale_le_geometric ht hsmall n).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num) : (1/2 : ℝ)^n ≤ 1) ht

lemma correctionScale_tendsto_zero {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1/32) :
    Tendsto (correctionScale t) atTop (𝓝 0) :=
  (correctionScale_summable ht hsmall).1.tendsto_atTop_zero

lemma correctionScale_tsum_le {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1/32) :
    (∑' n, correctionScale t n) ≤ 2*t := by
  have hgeom : Summable (fun n : ℕ => t*(1/2 : ℝ)^n) :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)).mul_left t
  have hh := (correctionScale_summable ht hsmall).1.tsum_le_tsum
    (correctionScale_le_geometric ht hsmall) hgeom
  rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)] at hh
  convert hh using 1
  ring

lemma correctionScale_partial_sum_le {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1/32) (N : ℕ) :
    ∑ n ∈ Finset.range N, correctionScale t n ≤ 2*t := by
  apply le_trans _ (correctionScale_tsum_le ht hsmall)
  exact (correctionScale_summable ht hsmall).1.sum_le_tsum (Finset.range N)
    (fun n _ => correctionScale_nonneg ht n)

lemma correction_displacement_budget {t ρ : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1/32)
    (hρ : 0 ≤ ρ) (N : ℕ) :
    ρ/8 + ρ*(∑ n ∈ Finset.range N, correctionScale t n) ≤ ρ/4 := by
  have hh := mul_le_mul_of_nonneg_left (correctionScale_partial_sum_le ht hsmall N) hρ
  have hs := mul_le_mul_of_nonneg_left hsmall hρ
  nlinarith

end ClosedSurfaceR4.ExactCorrection

end

end OAI
