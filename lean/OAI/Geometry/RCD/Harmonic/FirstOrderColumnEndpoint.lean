import OAI.Geometry.RCD.Transport.ColumnPlanGramEndpoint
import OAI.Geometry.RCD.Coordinates.FirstOrderRegularFamily
import OAI.Geometry.RCD.Harmonic.GramDefectLocality

namespace OAI

/-! # Integrated Gram endpoint bounds for the original coordinates -/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.first_order_column_endpoint {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {p : X} {r ε : ℝ}
    (hr : 0<r) (hε : 0≤ε) (hε1 : ε≤1)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n)
    (hsplit : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16*r) ε u v)
    (a : Euclidean n) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p≤r/12)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p≤r/12) :
    ∀ᵐ γ ∂π,
      ⟪v (γ 1)-v (γ 0),a⟫_ℝ^2≤(dist (γ 0) (γ 1))^2*‖a‖^2*
        (1+∫ t in Icc (0:ℝ) 1, gramDefect (hausdorff n X) hX.quadratic u (geodesicExtension γ t)) := by
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
  have hcol := column_plan_gram_endpoint μ Q (fun i => (U i).val) F hF hW a π hgeo hC hcomp hD
    measurableSet_ball hstay (gramDefect_integrableOn μ Q _ (hX.finiteOnBounded _ isBounded_ball).ne)
  have he := testPlan_eval_property_on μ π hcomp measurableSet_ball hstay (gramDefect_congr_ae μ Q hu)
  filter_upwards [hcol,he,hstay] with γ hcol he hs
  rw [hFv (hs 0),hFv (hs 1),integral_congr_ae he] at hcol
  exact hcol

end RegularPointCoordinates

end

end OAI
