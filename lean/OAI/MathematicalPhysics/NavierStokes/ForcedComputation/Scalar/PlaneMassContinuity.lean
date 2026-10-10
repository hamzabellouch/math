import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarTail

namespace OAI

/-! Uniform integrable domination and continuity of whole-plane mass on
finite time intervals. Both are consequences of the local scalar estimates. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory
open scoped ContDiff

theorem PlaneScalarSolution.uniform_tail_bound
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 T, ∀ x, |w t x| ≤ B * planeTailProfile x := by
  obtain ⟨C, K, hC, hK, hb⟩ := hw.tail_bound hT hν ha hh hc
  refine ⟨C * Real.exp (K * T), mul_nonneg hC (Real.exp_pos _).le, ?_⟩
  have hn := hw.nonnegative hT hν ha hc hpos
  intro t ht x
  rw [abs_of_nonneg (hn t ht x)]
  apply (hb t ht x).trans
  apply mul_le_mul_of_nonneg_right _ (planeTailProfile_pos x).le
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK)) hC

theorem PlaneScalarSolution.mass_continuousOn
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x) :
    ContinuousOn (fun t => ∫ x, w t x) (Icc 0 T) := by
  obtain ⟨B, _, hB⟩ := hw.uniform_tail_bound hT hν ha hh hc hpos
  apply continuousOn_of_dominated
    (fun t ht => (hw.slice_smooth ht).continuous.aestronglyMeasurable)
    (bound := fun x => B * planeTailProfile x)
  · intro t ht
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using hB t ht x
  · exact planeTailProfile_integrable.const_mul B
  · filter_upwards [] with x
    exact hw.smooth.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ht => ⟨ht, mem_univ x⟩)

end ForcedComputation.VelocityDetector

end

end OAI
