import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic
import OAI.Analysis.RieszRectifiability.Projections.ProjectionCells
import OAI.Analysis.RieszRectifiability.Flatness.AffinePlaneCoordinates

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function
open scoped NNReal ENNReal

theorem GlobalUpperGrowth.mono_constant {d n : ℕ} {C D : ℝ}
    {μ : Measure (Ambient d)} (h : GlobalUpperGrowth n C μ) (hCD : C ≤ D) :
    GlobalUpperGrowth n D μ := by
  refine ⟨h.1.trans hCD, ?_⟩
  intro x r hr
  exact (h.2 x r hr).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCD (pow_nonneg hr.le n)))

theorem boxPlaneMeasure_upper_growth {ι : Type*} [Fintype ι] {d : ℕ}
    (I : Box ι) (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (he : Measurable e) (Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) :
    GlobalUpperGrowth (Fintype.card ι) ((2 * (Q : ℝ)) ^ Fintype.card ι)
      (boxPlaneMeasure I e) := by
  refine ⟨by positivity, ?_⟩
  intro x r hr
  rw [boxPlaneMeasure, Measure.map_apply he measurableSet_ball,
    Measure.restrict_apply (measurableSet_ball.preimage he)]
  calc
    volume ((e ⁻¹' ball x r) ∩ (I : Set (ι → ℝ))) ≤
        volume (closedBall (π x) ((Q : ℝ) * r)) := by
      apply measure_mono
      intro u hu
      apply mem_closedBall.mpr
      have hu' : dist (e u) x < r := hu.1
      calc
        dist u (π x) = dist (π (e u)) (π x) := by rw [hleft u]
        _ ≤ (Q : ℝ) * dist (e u) x := hπ.dist_le_mul _ _
        _ ≤ (Q : ℝ) * r := mul_le_mul_of_nonneg_left hu'.le Q.coe_nonneg
    _ = ENNReal.ofReal ((2 * ((Q : ℝ) * r)) ^ Fintype.card ι) :=
      Real.volume_pi_closedBall (π x) (mul_nonneg Q.coe_nonneg hr.le)
    _ = ENNReal.ofReal ((2 * (Q : ℝ)) ^ Fintype.card ι * r ^ Fintype.card ι) := by
      congr 1
      rw [← mul_assoc, mul_pow]

theorem affinePlaneBox_upper_growth {n d : ℕ} (I : Box (Fin n)) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) :
    GlobalUpperGrowth n ((2 * (‖L.toContinuousLinearMap.adjoint‖₊ : ℝ)) ^ n)
      (boxPlaneMeasure I (affinePlaneSection a L)) := by
  simpa only [Fintype.card_fin] using! boxPlaneMeasure_upper_growth I
    (affinePlaneSection a L) (affinePlaneCoordinates a L)
    (affinePlaneSection_lipschitz a L).continuous.measurable
    ‖L.toContinuousLinearMap.adjoint‖₊ (affinePlaneCoordinates_lipschitz a L)
    (affinePlaneCoordinates_leftInverse a L)

end

end RieszRectifiability

end OAI
