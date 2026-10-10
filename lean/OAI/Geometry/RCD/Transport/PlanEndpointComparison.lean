import OAI.Geometry.RCD.Transport.NearbyBallPlan

namespace OAI

/-! # Endpoint value and cost errors for small-ball transport plans -/

open Set Filter Metric MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem endpoint_ball_plan_cost_bound (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hL : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (x y : X) {ρ : ℝ}
    (hs : ∀ᵐ γ ∂π, dist (γ 0) x < ρ ∧ dist (γ 1) y < ρ) :
    (∫ γ : C(Time,X), (dist (γ 0) (γ 1))^2 ∂π) ≤ (dist x y+2*ρ)^2 := by
  have hb : ∀ᵐ γ ∂π, (dist (γ 0) (γ 1))^2 ≤ (dist x y+2*ρ)^2 := by
    filter_upwards [hs] with γ hγ
    have h0 := dist_triangle (γ 0) x y
    have h1 := dist_triangle (γ 0) y (γ 1)
    rw [dist_comm y (γ 1)] at h1
    apply pow_le_pow_left₀ dist_nonneg
    linarith [hγ.1,hγ.2]
  have hi := integral_mono_ae hL.integrable_sq (integrable_const ((dist x y+2*ρ)^2)) hb
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hi

theorem plan_endpoint_lipschitz_error (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (f : X → ℝ) (hf : Measurable f) {Ω : Set X} {L : ℝ≥0}
    (hL : LipschitzOnWith L f Ω) (x : X) (hx : x ∈ Ω)
    (t : Time) {ρ : ℝ}
    (hs : ∀ᵐ γ ∂π, γ t ∈ Ω ∧ dist (γ t) x < ρ) :
    |(∫ γ : C(Time,X), f (γ t) ∂π)-f x| ≤ (L:ℝ)*ρ := by
  have hbound : ∀ᵐ γ ∂π, |f (γ t)-f x| ≤ (L:ℝ)*ρ := by
    filter_upwards [hs] with γ hγ
    have hh := hL.dist_le_mul _ hγ.1 x hx
    rw [Real.dist_eq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hγ.2.le L.coe_nonneg)
  have hi : Integrable (fun γ : C(Time,X) => f (γ t)-f x) π :=
    Integrable.of_bound ((hf.comp (measurable_path_eval t)).aestronglyMeasurable.sub aestronglyMeasurable_const)
      ((L:ℝ)*ρ) (by simpa only [Real.norm_eq_abs] using hbound)
  have hfint : Integrable (fun γ : C(Time,X) => f (γ t)) π := by
    have hh : Integrable (fun γ : C(Time,X) => (f (γ t)-f x)+f x) π :=
      hi.add (integrable_const (f x))
    simpa only [sub_add_cancel] using hh
  have he : (∫ γ : C(Time,X), f (γ t) ∂π)-f x =
      ∫ γ : C(Time,X), f (γ t)-f x ∂π := by
    rw [integral_sub hfint (integrable_const _),integral_const,
      probReal_univ,smul_eq_mul,one_mul]
  rw [he]
  calc
    _ ≤ ∫ γ : C(Time,X), |f (γ t)-f x| ∂π := abs_integral_le_integral_abs
    _ ≤ ∫ _ : C(Time,X), (L:ℝ)*ρ ∂π := integral_mono_ae hi.abs (integrable_const _) hbound
    _ = _ := by rw [integral_const,probReal_univ,smul_eq_mul,one_mul]

end RegularPointCoordinates

end

end OAI
