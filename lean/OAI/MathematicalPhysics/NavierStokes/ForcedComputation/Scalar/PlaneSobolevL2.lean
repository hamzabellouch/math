import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneTimeRegularity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneL2Lift

namespace OAI

/-! The scalar solution has continuous L2 representatives for all spatial
derivatives through order two, and is continuously differentiable in L2. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian MeasureTheory Set
open scoped ContDiff

def PlaneContinuousL2 (F : ℝ → Plane → ℝ) (S : Set ℝ) : Prop :=
  ∃ U : ℝ → PlaneL2, ContinuousOn U S ∧
    ∀ t ∈ S, (fun x => U t x) =ᵐ[volume] F t

def PlaneCInH2 (F : ℝ → Plane → ℝ) (S : Set ℝ) : Prop :=
  PlaneContinuousL2 F S ∧
    (∀ j, PlaneContinuousL2 (fun t => spatialD j (F t)) S) ∧
    (∀ j k, PlaneContinuousL2 (fun t => spatialD j (spatialD k (F t))) S)

theorem PlaneScalarSolution.cInH2 (hE : PlaneScalarExistence)
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 < T) (hν : 0 < ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x) : PlaneCInH2 w (Icc 0 T) := by
  have hi := fun t ht => hw.square_integrable_jet2 hE hT.le hν ha hh hc hpos (t := t) ht
  obtain ⟨h0, h1, h2⟩ := hw.h2_continuousOn hE hT hν ha hh hc hpos
  refine ⟨?_, ?_, ?_⟩
  · apply exists_planeL2_continuous_representation _ h0
    intro t ht
    exact (memLp_two_iff_integrable_sq (hw.slice_smooth ht).continuous.aestronglyMeasurable).mpr
      (hi t ht).1
  · intro j
    apply exists_planeL2_continuous_representation _ (h1 j)
    intro t ht
    exact (memLp_two_iff_integrable_sq
      (spatialD_smooth j (hw.slice_smooth ht)).continuous.aestronglyMeasurable).mpr
        ((hi t ht).2.1 j)
  · intro j k
    apply exists_planeL2_continuous_representation _ (h2 j k)
    intro t ht
    exact (memLp_two_iff_integrable_sq
      (spatialD_smooth j (spatialD_smooth k (hw.slice_smooth ht))).continuous.aestronglyMeasurable).mpr
        ((hi t ht).2.2 j k)

theorem PlaneScalarSolution.c1L2 (hE : PlaneScalarExistence)
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 < T) (hν : 0 < ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x) :
    PlaneC1L2 w (planeTimeDerivative ν a h w) (Icc 0 T) := by
  obtain ⟨B, hB, hb⟩ := hw.time_derivative_envelope hE hT.le hν ha hh hc hpos
  have hs (t : ℝ) (ht : t ∈ Icc 0 T) : Continuous (planeTimeDerivative ν a h w t) :=
    hw.timeDerivative_slice_continuous ha hh ht
  have hm (t : ℝ) (ht : t ∈ Icc 0 T) : MemLp (planeTimeDerivative ν a h w t) 2 volume := by
    apply (memLp_two_iff_integrable_sq (hs t ht).aestronglyMeasurable).mpr
    apply (derivativeTail_square_integrable.const_mul (B ^ 2)).mono'
      ((hs t ht).pow 2).aestronglyMeasurable
    filter_upwards [] with x
    change ‖planeTimeDerivative ν a h w t x ^ 2‖ ≤ B ^ 2 * derivativeTail x ^ 2
    have hh' := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hB (derivativeTail_pos x).le)).mpr
      (hb t ht x)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (planeTimeDerivative ν a h w t x)]
  have hwm (t : ℝ) (ht : t ∈ Icc 0 T) : MemLp (w t) 2 volume :=
    (memLp_two_iff_integrable_sq (hw.slice_smooth ht).continuous.aestronglyMeasurable).mpr
      (hw.square_integrable_jet2 hE hT.le hν ha hh hc hpos ht).1
  obtain ⟨hd, hcG⟩ := hw.strong_time_regularity hE hT hν ha hh hc hpos
  exact planeC1L2_of_square_estimates hwm hm
    (hw.h2_continuousOn hE hT hν ha hh hc hpos).1 hcG hd

end ForcedComputation.VelocityDetector

end

end OAI
