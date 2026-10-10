import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.LatticeMassPacking
import OAI.Analysis.RieszRectifiability.Surfaces.PlaneDiskLowerArea
import OAI.Analysis.RieszRectifiability.Foundations.NativeHausdorffGrowth

namespace OAI

/-!
# A uniform fraction for core area

The core-area fraction depends only on the dimension and upper growth
constant. Its coefficient bound compares lattice-cell mass with the
Hausdorff measure of a plane disk at the smaller core scale.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def nativeCoreAreaFraction (n : ℕ) (G : ℝ) : ℝ :=
  min (1 / 2) ((planeUnitHausdorffMeasure n).toReal /
    (2 * (G * (3 : ℝ) ^ n * (32 : ℝ) ^ n)))

theorem nativeCoreAreaFraction_pos_le_half (n : ℕ) (G : ℝ) (hG : 0 < G) :
    0 < nativeCoreAreaFraction n G ∧ nativeCoreAreaFraction n G ≤ 1 / 2 := by
  have hu : 0 < (planeUnitHausdorffMeasure n).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨planeUnitHausdorffMeasure_pos n, planeUnitHausdorffMeasure_lt_top n⟩
  exact ⟨lt_min (by norm_num) (by positivity), min_le_left _ _⟩

theorem nativeCoreAreaFraction_coefficient_bound (n : ℕ) (G : ℝ) (hG : 0 < G) :
    2 * nativeCoreAreaFraction n G * (G * (3 : ℝ) ^ n) ≤
      (planeUnitHausdorffMeasure n).toReal / (32 : ℝ) ^ n := by
  have h := min_le_right (1 / 2 : ℝ)
    ((planeUnitHausdorffMeasure n).toReal / (2 * (G * (3 : ℝ) ^ n * (32 : ℝ) ^ n)))
  change nativeCoreAreaFraction n G ≤ _ at h
  have hb := (le_div_iff₀ (by positivity : 0 < 2 * (G * (3 : ℝ) ^ n * (32 : ℝ) ^ n))).mp h
  apply (le_div_iff₀ (by positivity : 0 < (32 : ℝ) ^ n)).mpr
  nlinarith

theorem native_core_disk_area_ge_double_fraction {n d : ℕ}
    (ν : Measure (Ambient d)) (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets ν R hR k).points)
    (a : Ambient n) :
    ENNReal.ofReal (2 * nativeCoreAreaFraction n G) * ν (cleanSupportCell ν R hR k z) ≤
      (μH[(n : ℝ)] : Measure (Ambient n)) (closedBall a (latticeRadius R k / 32)) := by
  have hr := latticeRadius_pos R hR k
  have hθ := (nativeCoreAreaFraction_pos_le_half n G hG).1
  have htop : ν (cleanSupportCell ν R hR k z) ≤ ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := by
    have hb := (supportLatticeCell_bounds ν R hR k z).2
    have hsub : cleanSupportCell ν R hR k z ⊆ ball (z : Ambient d) (3 * latticeRadius R k) :=
      sdiff_subset.trans (hb.trans (closedBall_subset_ball (by have hr := latticeRadius_pos R hR k; linarith)))
    exact (measure_mono hsub).trans (hg.2 z _ (by positivity))
  have hcoeff := nativeCoreAreaFraction_coefficient_bound n G hG
  have hreal : (2 * nativeCoreAreaFraction n G) * (G * (3 * latticeRadius R k) ^ n) ≤
      (latticeRadius R k / 32) ^ n * (planeUnitHausdorffMeasure n).toReal := by
    have h := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (latticeRadius_pos R hR k).le n)
    calc
      _ = (2 * nativeCoreAreaFraction n G * (G * (3 : ℝ) ^ n)) * (latticeRadius R k) ^ n := by
        rw [mul_pow]; ring
      _ ≤ ((planeUnitHausdorffMeasure n).toReal / (32 : ℝ) ^ n) * (latticeRadius R k) ^ n := h
      _ = _ := by rw [div_pow]; ring
  calc
    _ ≤ ENNReal.ofReal (2 * nativeCoreAreaFraction n G) *
        ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := mul_le_mul' le_rfl htop
    _ = ENNReal.ofReal ((2 * nativeCoreAreaFraction n G) * (G * (3 * latticeRadius R k) ^ n)) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal ((latticeRadius R k / 32) ^ n * (planeUnitHausdorffMeasure n).toReal) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ambient_closedBall_hausdorffMeasure n a _ (by positivity),
        ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_toReal (planeUnitHausdorffMeasure_lt_top n).ne,
        ENNReal.ofReal_pow (by positivity)]

end

end RieszRectifiability

end OAI
