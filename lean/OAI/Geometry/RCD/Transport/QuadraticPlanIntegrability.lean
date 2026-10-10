import OAI.Geometry.RCD.Transport.QuadraticMidpointError
import OAI.Geometry.RCD.Transport.BoundedGeodesicPlan

namespace OAI

/-! # Integrability of distance defects on bounded geodesic plans -/

open Set Filter Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem quadratic_plan_integrable_data (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ) (z : X) {R : ℝ} (hR : 0≤R)
    (h0 : ∀ᵐ γ ∂π, dist z (γ 0)≤R) (h1 : ∀ᵐ γ ∂π, dist z (γ 1)≤R) :
    (∀ s : Time, Integrable (fun γ => dist z (γ s)^2/2) π) ∧
    Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) π := by
  constructor
  · intro s
    have hcont : Continuous (fun γ : C(Time,X) => dist z (γ s)^2/2) :=
      ((continuous_const.dist (continuous_eval_const s)).pow 2).div_const 2
    apply Integrable.of_bound hcont.aestronglyMeasurable ((3*R)^2/2)
    filter_upwards [geodesic_plan_ball_support π hg z h0 h1] with γ hγ
    have hd : dist z (γ s)≤3*R := by simpa only [mem_closedBall,dist_comm] using hγ s
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    nlinarith [dist_nonneg (x:=z) (y:=γ s)]
  · have hcont : Continuous (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) :=
      ((continuous_eval_const 0).dist (continuous_eval_const 1)).pow 2
    apply Integrable.of_bound hcont.aestronglyMeasurable (4*R^2)
    filter_upwards [h0,h1] with γ ha hb
    have hd : dist (γ 0) (γ 1)≤2*R := by
      have hh := dist_triangle (γ 0) z (γ 1)
      rw [dist_comm (γ 0) z] at hh
      linarith
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith [dist_nonneg (x:=γ 0) (y:=γ 1)]

omit [MeasurableSpace X] [BorelSpace X] in
theorem quadratic_plan_interior_integrable (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ) (z : X) {R : ℝ} (hR : 0≤R)
    (h0 : ∀ᵐ γ ∂π, dist z (γ 0)≤R) (h1 : ∀ᵐ γ ∂π, dist z (γ 1)≤R)
    (l h t : Time) :
    Integrable (interiorQuadraticDefect (fun x => dist z x^2/2) l h t) π := by
  obtain ⟨hi,hd⟩ := quadratic_plan_integrable_data π hg z hR h0 h1
  exact ((hi t).sub (hi l) |>.sub (((hi h).sub (hi l)).div_const _ |>.mul_const _)).sub
    ((hd.mul_const _).mul_const _ |>.div_const _)

end RegularPointCoordinates

end

end OAI
