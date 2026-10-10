import OAI.Geometry.RCD.Sobolev.ContinuousPathMean

namespace OAI

/-! # The interior quadratic defect along an actual path -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

def interiorQuadraticDefect (U : X → ℝ) (l h t : Time) (γ : C(Time,X)) : ℝ :=
  U (γ t)-U (γ l)-((U (γ h)-U (γ l))/((h:ℝ)-l))*((t:ℝ)-l)-
    dist (γ 0) (γ 1)^2*((t:ℝ)-l)*((t:ℝ)-h)/2

omit [MeasurableSpace X] [BorelSpace X] in
theorem interiorQuadraticDefect_continuous {U : X → ℝ} (hU : Continuous U) (l h t : Time) :
    Continuous (interiorQuadraticDefect U l h t) := by
  unfold interiorQuadraticDefect
  fun_prop

theorem interiorQuadraticDefect_integrable (μ : Measure C(Time,X)) [IsFiniteMeasure μ]
    {U : X → ℝ} (hU : Continuous U) (hUc : HasCompactSupport U)
    (hd : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) μ) (l h t : Time) :
    Integrable (interiorQuadraticDefect U l h t) μ := by
  obtain ⟨M,hM⟩ := hUc.exists_bound_of_continuous hU
  have hi (s : Time) : Integrable (fun γ : C(Time,X) => U (γ s)) μ :=
    Integrable.of_bound (hU.measurable.comp (measurable_path_eval s)).aestronglyMeasurable M
      (Eventually.of_forall fun γ => hM (γ s))
  exact ((hi t).sub (hi l) |>.sub (((hi h).sub (hi l)).div_const _ |>.mul_const _)).sub
    ((hd.mul_const _).mul_const _ |>.div_const _)

theorem integral_interiorQuadraticDefect (μ : Measure C(Time,X)) [IsFiniteMeasure μ]
    {U : X → ℝ} (hU : Continuous U) (hUc : HasCompactSupport U)
    (hd : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) μ) (l h t : Time) :
    (∫ γ, interiorQuadraticDefect U l h t γ ∂μ)=
      (∫ γ, U (γ t) ∂μ)-(∫ γ, U (γ l) ∂μ)-
        (((∫ γ, U (γ h) ∂μ)-(∫ γ, U (γ l) ∂μ))/((h:ℝ)-l))*((t:ℝ)-l)-
          (∫ γ, dist (γ 0) (γ 1)^2 ∂μ)*((t:ℝ)-l)*((t:ℝ)-h)/2 := by
  obtain ⟨M,hM⟩ := hUc.exists_bound_of_continuous hU
  have hi (s : Time) : Integrable (fun γ : C(Time,X) => U (γ s)) μ :=
    Integrable.of_bound (hU.measurable.comp (measurable_path_eval s)).aestronglyMeasurable M
      (Eventually.of_forall fun γ => hM (γ s))
  unfold interiorQuadraticDefect
  have hlin : Integrable (fun γ => (U (γ h)-U (γ l))/((h:ℝ)-l)*((t:ℝ)-l)) μ :=
    ((hi h).sub (hi l)).div_const _ |>.mul_const _
  have hquad : Integrable (fun γ : C(Time,X) =>
      dist (γ 0) (γ 1)^2*((t:ℝ)-l)*((t:ℝ)-h)/2) μ :=
    (hd.mul_const _).mul_const _ |>.div_const _
  rw [integral_sub
      (f := fun γ : C(Time,X) => U (γ t)-U (γ l)-(U (γ h)-U (γ l))/((h:ℝ)-l)*((t:ℝ)-l))
      (g := fun γ : C(Time,X) => dist (γ 0) (γ 1)^2*((t:ℝ)-l)*((t:ℝ)-h)/2)
      (((hi t).sub (hi l)).sub hlin) hquad,
    integral_sub (f := fun γ : C(Time,X) => U (γ t)-U (γ l))
      (g := fun γ : C(Time,X) => (U (γ h)-U (γ l))/((h:ℝ)-l)*((t:ℝ)-l))
      ((hi t).sub (hi l)) hlin,
    integral_sub (hi t) (hi l),integral_mul_const,integral_div,integral_sub (hi h) (hi l),
    integral_div,integral_mul_const,integral_mul_const]

end RegularPointCoordinates

end

end OAI
