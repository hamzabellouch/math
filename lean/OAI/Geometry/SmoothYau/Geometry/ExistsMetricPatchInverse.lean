import Mathlib
import OAI.Geometry.SmoothYau.Estimates.RescaledDifferentialPerturbation
import OAI.Geometry.SmoothYau.Smoothness.ExistsFinitePatchPartition
import OAI.Geometry.SmoothYau.Smoothness.LocalIntegrationParts

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


theorem exists_metric_patch_inverse (g : SmoothMetric E M) (p : M)
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      Metric.closedBall ((chartAt E p) p) r ⊆ (chartAt E p).target ∧
      ∀ α : ℝ, 1 ≤ α →
        ∃ R : FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s + 2),
          ‖R‖ ≤ C ∧
          (∀ f, ‖sobolevInclusion (s + 2) (s + 1) (by linarith) (R f)‖ ≤
            C * (Real.sqrt α)⁻¹ * ‖f‖) ∧
          (∀ (ht : Module.finrank ℝ E < 2 * (s + 2))
              (f : FourierSobolevSpace E ℂ s) (x : E), ‖x‖ ≤ 1 →
              (α : ℂ) * sobolevRepresentative ht (R f) x -
              (∑ i, ∑ j, ((metricCoefficients g p ((chartAt E p) p + r • x))⁻¹ i j : ℂ) *
                fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht (R f) : E → ℂ)
                  y (Module.finBasis ℝ E j)) x (Module.finBasis ℝ E i)) -
              (r : ℂ) * ∑ i, (metricFirstCoefficient g p i ((chartAt E p) p + r • x) : ℂ) *
                fderiv ℝ (sobolevRepresentative ht (R f) : E → ℂ) x (Module.finBasis ℝ E i) =
              sobolevRepresentative hs f x) := by
  obtain ⟨a, c, ha, hc, hA, δ, hδ, hd, hcoeff⟩ := exists_smooth_metric_coefficients_at g p
  let A : Matrix (CoordIndex E) (CoordIndex E) ℝ := fun i j => a i j ((chartAt E p) p)
  let L := physicalQuadraticEquiv (Module.finBasis ℝ E) A hA
  obtain ⟨ε, hε, he⟩ := exists_rescaled_local_inverse (Module.finBasis ℝ E) a c ha hc
    (complexUnitBump E) (contDiff_complexUnitBump E) (hasCompactSupport_complexUnitBump E)
    ((chartAt E p) p) hs hA
  let r := min ε δ / 2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have hrε : r < ε := (half_lt_self (lt_min hε hδ)).trans_le (min_le_left _ _)
  have hrδ : r < δ := (half_lt_self (lt_min hε hδ)).trans_le (min_le_right _ _)
  let C := 2 * anisotropicConstant L
  have hC : 0 < C := by
    dsimp [C, anisotropicConstant]
    positivity
  refine ⟨r, C, hr, hC, ?_, fun α hα => ?_⟩
  · exact (Metric.closedBall_subset_ball hrδ).trans hd
  · obtain ⟨R, hR, hR1, hRe⟩ := he r (by simpa only [abs_of_pos hr] using hrε) α hα
    refine ⟨R, hR, ?_, ?_⟩
    · intro f
      simpa only [C, mul_assoc] using hR1 f
    · intro ht f x hx
      have hdist : (chartAt E p) p + r • x ∈ Metric.ball ((chartAt E p) p) δ := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_pos hr]
        exact (mul_le_of_le_one_right hr.le hx).trans_lt hrδ
      obtain ⟨hae, hce⟩ := hcoeff _ hdist
      have hh := hRe ht f x (complexUnitBump_eq_one E hx)
      simpa only [hae, hce] using hh
end YauCounterexamples


end

end OAI
