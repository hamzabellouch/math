import OAI.Geometry.RCD.Coordinates.LocalFramePathVelocity
import OAI.Geometry.RCD.Coordinates.FirstOrderRegularFamily

namespace OAI

/-! # Actual first-order coordinates give scalar path velocities -/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.first_order_path_velocity {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {p : X} {r ε : ℝ}
    (hr : 0<r) (hε : 0≤ε) (hε1 : ε≤1)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n)
    (hsplit : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16*r) ε u v)
    (g : SobolevSpace (hausdorff n X) hX.quadratic) (φ : X → ℝ) (hφ : Continuous φ)
    (hg : SobolevSpace.toLp (hausdorff n X) hX.quadratic g =ᵐ[hausdorff n X] φ)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p≤r/12)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p≤r/12) :
    ∀ᵐ γ ∂π,
      AbsolutelyContinuousOnInterval (fun t => φ (geodesicExtension γ t)) 0 1 ∧
      (∀ i, AbsolutelyContinuousOnInterval (fun t => v (geodesicExtension γ t) i) 0 1) ∧
      ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 →
        (deriv (fun s => φ (geodesicExtension γ s)) t-
          ∑ i, localGamma (hausdorff n X) hX.quadratic (u i) g (geodesicExtension γ t)*
            deriv (fun s => v (geodesicExtension γ s) i) t)^2≤
          (dist (γ 0) (γ 1))^2*
            frameVelocityError (hausdorff n X) hX.quadratic u g (geodesicExtension γ t) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  obtain ⟨U,d,W,_L,_A,_hd,_hL,_hWc,hW,_hA,hu,_hd0,hv,_hgrad⟩ :=
    hX.first_order_regular_family hn hr hε hε1 u v hsplit
  let F (x : X) : Euclidean n := WithLp.toLp 2 (fun i => W i x)
  have hF : Continuous F := (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
    (continuous_pi (fun i => (W i).continuous))
  have hFv : EqOn F v (ball p (6*r)) := by
    intro x hx
    apply PiLp.ext
    intro i
    exact hv i hx
  have hbounded := optimal_geodesic_plan_bounded (π.map (fun γ => γ 0))
    (π.map (fun γ => γ 1)) π hgeo hopt p (show 0≤r/12 by linarith) hs₀ hs₁
  have hstay : ∀ᵐ γ ∂π, ∀ t : Time, γ t∈ball p (6*r) := by
    filter_upwards [hbounded] with γ hγ t
    exact (hγ.2 t).trans_lt (by linarith)
  have hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π := by
    apply MemLp.of_bound ((continuous_eval_const 0).dist (continuous_eval_const 1)).aestronglyMeasurable r
    filter_upwards [hbounded] with γ hγ
    rw [Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
    have hh := dist_triangle (γ 0) p (γ 1)
    rw [dist_comm p (γ 1)] at hh
    linarith [hγ.2 0,hγ.2 1]
  exact local_frame_path_velocity μ Q u (fun i => (U i).val) g v F φ hF hφ hW hg
    measurableSet_ball hu hFv π hgeo hC hcomp hD hstay

end RegularPointCoordinates

end

end OAI
