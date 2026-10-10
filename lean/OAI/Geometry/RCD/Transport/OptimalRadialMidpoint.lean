import OAI.Geometry.RCD.Transport.RadialMidpointRigidity

namespace OAI

/-! # An optimal replacement to a radial midpoint remains radial

The finite quadratic transport cost and the midpoint marginal determine
both radial moments. Equality in the integrated triangle inequality
therefore forces the same pole on every replacement path.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem optimal_radial_midpoint
    (q : Measure C(Time, X)) [IsProbabilityMeasure q] (p : X)
    (hq : ∀ᵐ γ ∂q, IsGeodesic γ) (hend : q.map (fun γ => γ 1) = Measure.dirac p)
    (hfinite : transportCost (q.map (fun γ => (γ 0, γ 1))) ≠ ∞)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hp : IsOptimalCoupling (q.map (fun γ => γ 0)) (q.map (fun γ => γ midpointTime))
      (π.map (fun γ => (γ 0, γ 1)))) :
    ∀ᵐ γ ∂π, dist (γ 0) (γ 1) = dist (γ 1) p ∧
      dist (γ 0) p = dist (γ 0) (γ 1) + dist (γ 1) p := by
  have hf (s t : Time) : (q.map (fun γ => (γ s, γ t))).map Prod.fst =
      q.map (fun γ => γ s) := by
    rw [Measure.map_map measurable_fst ((measurable_path_eval s).prodMk (measurable_path_eval t))]
    rfl
  have hs (s t : Time) : (q.map (fun γ => (γ s, γ t))).map Prod.snd =
      q.map (fun γ => γ t) := by
    rw [Measure.map_map measurable_snd ((measurable_path_eval s).prodMk (measurable_path_eval t))]
    rfl
  have hm : Measurable (fun x : X => ENNReal.ofReal (dist x p) ^ 2) := by fun_prop
  have hπends := optimalPlan_endpoints _ _ π hp
  let C := transportCost (q.map (fun γ => (γ 0, γ 1)))
  have hC0 : C = ∫⁻ γ, ENNReal.ofReal (dist (γ 0) p) ^ 2 ∂π := by
    have he := transportCost_eq_moment_of_dirac (q.map (fun γ => γ 0)) p
      (q.map (fun γ => (γ 0, γ 1))) (hf 0 1) ((hs 0 1).trans hend)
    rw [← hπends.1, lintegral_map hm (measurable_path_eval 0)] at he
    exact he
  have hhalfcost : transportCost (q.map (fun γ => (γ 0, γ midpointTime))) = (4 : ℝ≥0∞)⁻¹ * C := by
    rw [geodesic_plan_cost q hq 0 midpointTime]
    congr 1
    norm_num [midpointTime, ENNReal.ofReal_div_of_pos, ← ENNReal.inv_pow]
  have hπcost : (∫⁻ γ, ENNReal.ofReal (dist (γ 0) (γ 1)) ^ 2 ∂π) ≤ (4 : ℝ≥0∞)⁻¹ * C := by
    rw [← transportCost_plan_lintegral]
    rw [← hhalfcost]
    exact hp.2.2 _ (hf 0 midpointTime) (hs 0 midpointTime)
  have hC1 : (∫⁻ γ, ENNReal.ofReal (dist (γ 1) p) ^ 2 ∂π) = (4 : ℝ≥0∞)⁻¹ * C := by
    have he := transportCost_eq_moment_of_dirac (q.map (fun γ => γ midpointTime)) p
      (q.map (fun γ => (γ midpointTime, γ 1))) (hf midpointTime 1)
      ((hs midpointTime 1).trans hend)
    rw [← hπends.2, lintegral_map hm (measurable_path_eval 1)] at he
    rw [← he, geodesic_plan_cost q hq midpointTime 1]
    congr 1
    norm_num [midpointTime, ENNReal.ofReal_div_of_pos, ← ENNReal.inv_pow]
  obtain ⟨_, hr⟩ := quadratic_gluing_saturation π
    (fun γ => dist (γ 0) (γ 1)) (fun γ => dist (γ 1) p) (fun γ => dist (γ 0) p)
    ((measurable_path_eval 0).dist (measurable_path_eval 1))
    ((measurable_path_eval 1).dist measurable_const)
    ((measurable_path_eval 0).dist measurable_const)
    (Eventually.of_forall fun _ => dist_nonneg) (Eventually.of_forall fun _ => dist_nonneg)
    (Eventually.of_forall fun _ => dist_nonneg)
    (Eventually.of_forall fun γ => dist_triangle (γ 0) (γ 1) p)
    C hfinite hπcost hC1.le hC0.le
  filter_upwards [hr] with γ hγ
  refine ⟨hγ.1, ?_⟩
  linarith [hγ.1, hγ.2]

end RegularPointCoordinates

end OAI
