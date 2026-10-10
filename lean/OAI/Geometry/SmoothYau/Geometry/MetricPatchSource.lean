import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ScalarAffineDetNeZero
import OAI.Geometry.SmoothYau.Limits.LocalMetricInverse
import OAI.Geometry.SmoothYau.Smoothness.SobolevRepresentativeOrderCongr

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def metricPatchSource (p : M) (r : ℝ) (k : ℕ) :
    FourierSobolevSpace E ℂ (2 * (k : ℝ)) →L[ℂ] FourierSobolevSpace E ℂ (2 * (k : ℝ)) :=
  (r : ℂ) ^ 2 • sobolevAffineCutoff (complexUnitBump E) (hasCompactSupport_complexUnitBump E)
    (contDiff_complexUnitBump E) ((chartAt E p) p) r k

def metricPatchRawInverse (g : SmoothMetric E M) (p : M) (k : ℕ)
    (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (D : LocalMetricInverse g p (2 * (k : ℝ)) hs)
    (α : ℝ) (hα : 1 ≤ α * D.radius ^ 2) :
    FourierSobolevSpace E ℂ (2 * (k : ℝ)) →L[ℂ]
      FourierSobolevSpace E ℂ (2 * (k : ℝ) + 2) :=
  D.inverse (α * D.radius ^ 2) hα ∘L metricPatchSource (E := E) p D.radius k

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma metricPatchSource_representative (p : M) (r : ℝ) (hr : r ≠ 0) (k : ℕ)
    (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (f : FourierSobolevSpace E ℂ (2 * (k : ℝ))) (y : E) (hy : ‖y‖ ≤ 1) :
    sobolevRepresentative hs (metricPatchSource (E := E) p r k f) y =
      (r : ℂ) ^ 2 * sobolevRepresentative hs f ((chartAt E p) p + r • y) := by
  simp only [metricPatchSource, smul_apply, map_smul, BoundedContinuousFunction.smul_apply,
    smul_eq_mul]
  rw [sobolevAffineCutoff_representative (complexUnitBump E)
    (hasCompactSupport_complexUnitBump E) (contDiff_complexUnitBump E)
    ((chartAt E p) p) hr k hs f y, complexUnitBump_eq_one E hy, one_mul]

lemma metricPatchRawInverse_half_bound (g : SmoothMetric E M) (p : M) (k : ℕ)
    (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (D : LocalMetricInverse g p (2 * (k : ℝ)) hs)
    (α : ℝ) (hα : 1 ≤ α * D.radius ^ 2)
    (f : FourierSobolevSpace E ℂ (2 * (k : ℝ))) :
    ‖sobolevInclusion (2 * (k : ℝ) + 2) (2 * (k : ℝ) + 1) (by linarith)
        (metricPatchRawInverse g p k hs D α hα f)‖ ≤
      (D.bound * ‖metricPatchSource (E := E) p D.radius k‖) *
        (Real.sqrt (α * D.radius ^ 2))⁻¹ * ‖f‖ := by
  apply (D.half_bound _ hα _).trans
  calc
    D.bound * (Real.sqrt (α * D.radius ^ 2))⁻¹ * ‖metricPatchSource (E := E) p D.radius k f‖ ≤
      D.bound * (Real.sqrt (α * D.radius ^ 2))⁻¹ *
        (‖metricPatchSource (E := E) p D.radius k‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left ((metricPatchSource (E := E) p D.radius k).le_opNorm f)
        (mul_nonneg D.bound_pos.le (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    _ = _ := by ring

lemma metricPatchRawInverse_physical_equation (g : SmoothMetric E M) (p : M) (k : ℕ)
    (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (D : LocalMetricInverse g p (2 * (k : ℝ)) hs)
    (α : ℝ) (hα : 1 ≤ α * D.radius ^ 2)
    (ht : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 2))
    (f : FourierSobolevSpace E ℂ (2 * (k : ℝ))) (x : E)
    (hx : ‖D.radius⁻¹ • (x - (chartAt E p) p)‖ ≤ 1) :
    (α : ℂ) * sobolevRepresentative ht (metricPatchRawInverse g p k hs D α hα f)
        (D.radius⁻¹ • (x - (chartAt E p) p)) -
      euclideanElliptic (Module.finBasis ℝ E)
        (fun i j y => (metricCoefficients g p y)⁻¹ i j) (metricFirstCoefficient g p)
        (fun y => sobolevRepresentative ht (metricPatchRawInverse g p k hs D α hα f)
          (D.radius⁻¹ • (y - (chartAt E p) p))) x =
      sobolevRepresentative hs f x := by
  let w := metricPatchRawInverse g p k hs D α hα f
  have hw : ContDiff ℝ 2 (sobolevRepresentative ht w : E → ℂ) :=
    contDiff_sobolevRepresentative 2 (by norm_num; linarith) ht w
  apply unscale_local_equation (Module.finBasis ℝ E) _ _ ((chartAt E p) p)
    D.radius_pos.ne' α hw (sobolevRepresentative hs f) x
  have he := D.equation (α * D.radius ^ 2) hα ht (metricPatchSource (E := E) p D.radius k f)
    (D.radius⁻¹ • (x - (chartAt E p) p)) hx
  rw [metricPatchSource_representative p D.radius D.radius_pos.ne' k hs f _ hx] at he
  have hi : (chartAt E p) p + D.radius • (D.radius⁻¹ • (x - (chartAt E p) p)) = x := by
    simp only [smul_smul, mul_inv_cancel₀ D.radius_pos.ne', one_smul, add_sub_cancel]
  rw [hi] at he
  simpa only [euclideanElliptic, hi, Complex.ofReal_mul, mul_assoc, ← Finset.mul_sum, sub_add_eq_sub_sub,
    w, metricPatchRawInverse, ContinuousLinearMap.comp_apply] using he
end YauCounterexamples


end

end OAI
