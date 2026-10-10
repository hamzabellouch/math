import OAI.Geometry.RCD.Harmonic.WeightedRadialRigidity

namespace OAI

/-! # Optimal replacements of a radial-time marginal remain radial -/

open Set Filter Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace.SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem optimal_radial_time
    (q : Measure C(Time, X)) [IsProbabilityMeasure q] (p : X) {R : ℝ} (_hR : 0 ≤ R)
    (hq : ∀ᵐ γ ∂q, IsGeodesic γ ∧ ∀ s, dist (γ s) p ≤ R)
    (hend : q.map (fun γ => γ 1) = Measure.dirac p)
    (t : Time) (ht : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hπD : Integrable (fun γ : C(Time, X) => dist (γ 0) (γ 1) ^ 2) π)
    (hp : IsOptimalCoupling (q.map (fun γ => γ 0)) (q.map (fun γ => γ t))
      (π.map (fun γ => (γ 0, γ 1)))) :
    ∀ᵐ γ ∂π, dist (γ 0) (γ 1) = (t : ℝ) * dist (γ 0) p ∧
      dist (γ 1) p = (1 - (t : ℝ)) * dist (γ 0) p ∧
      dist (γ 0) p = dist (γ 0) (γ 1) + dist (γ 1) p := by
  have hf (s u : Time) : (q.map (fun γ => (γ s, γ u))).map Prod.fst =
      q.map (fun γ => γ s) := by
    rw [Measure.map_map measurable_fst ((measurable_path_eval s).prodMk (measurable_path_eval u))]
    rfl
  have hs (s u : Time) : (q.map (fun γ => (γ s, γ u))).map Prod.snd =
      q.map (fun γ => γ u) := by
    rw [Measure.map_map measurable_snd ((measurable_path_eval s).prodMk (measurable_path_eval u))]
    rfl
  have hqe : ∀ᵐ γ ∂q, γ 1 = p := by
    apply ae_of_ae_map (measurable_path_eval 1).aemeasurable (p := fun x : X => x = p)
    rw [hend]
    simp
  have hπends := optimalPlan_endpoints _ _ π hp
  have hpbd (s u : Time) (he : π.map (fun γ => γ s) = q.map (fun γ => γ u)) :
      ∀ᵐ γ ∂π, dist (γ s) p ≤ R := by
    apply ae_of_ae_map (measurable_path_eval s).aemeasurable
      (p := fun x : X => dist x p ≤ R)
    rw [he]
    apply (ae_map_iff (measurable_path_eval u).aemeasurable
      (measurableSet_le (measurable_id.dist measurable_const) measurable_const)).mpr
    exact hq.mono fun _ hγ => hγ.2 u
  have hi (ν : Measure C(Time, X)) [IsFiniteMeasure ν] (s : Time)
      (hb : ∀ᵐ γ ∂ν, dist (γ s) p ≤ R) :
      Integrable (fun γ : C(Time, X) => dist (γ s) p ^ 2) ν := by
    apply Integrable.mono' (integrable_const (R ^ 2))
      (((measurable_path_eval s).dist measurable_const).pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with γ hγ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ dist_nonneg hγ 2
  have hiq : Integrable (fun γ : C(Time, X) => dist (γ 0) (γ 1) ^ 2) q := by
    apply Integrable.mono' (integrable_const ((2 * R) ^ 2))
      (((measurable_path_eval 0).dist (measurable_path_eval 1)).pow_const 2).aestronglyMeasurable
    filter_upwards [hq] with γ hγ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ dist_nonneg _ 2
    have htri := dist_triangle (γ 0) p (γ 1)
    rw [dist_comm p (γ 1)] at htri
    linarith [hγ.2 0, hγ.2 1]
  let C := ∫ γ, dist (γ 0) (γ 1) ^ 2 ∂q
  have hC : 0 ≤ C := integral_nonneg fun _ => sq_nonneg _
  have hmd : Measurable (fun x : X => dist x p ^ 2) := by fun_prop
  have hC0 : (∫ γ, dist (γ 0) p ^ 2 ∂π) = C := by
    rw [← integral_map (measurable_path_eval 0).aemeasurable
      hmd.aestronglyMeasurable, hπends.1,
      integral_map (measurable_path_eval 0).aemeasurable
        hmd.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hqe] with γ hγ
    rw [hγ]
  have hC1 : (∫ γ, dist (γ 1) p ^ 2 ∂π) = (1 - (t : ℝ)) ^ 2 * C := by
    rw [← integral_map (measurable_path_eval 1).aemeasurable
      hmd.aestronglyMeasurable, hπends.2,
      integral_map (measurable_path_eval t).aemeasurable
        hmd.aestronglyMeasurable]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hq, hqe] with γ hγ he
    rw [← he, hγ.1 t 1]
    change (|(t : ℝ) - 1| * dist (γ 0) (γ 1)) ^ 2 = _
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr t.2.2), mul_pow]
  have hcostE := hp.2.2 (q.map (fun γ => (γ 0, γ t))) (hf 0 t) (hs 0 t)
  rw [transportCost_plan_eq_integral π hπD, geodesic_plan_cost q (hq.mono fun _ hγ => hγ.1) 0 t,
    transportCost_plan_eq_integral q hiq] at hcostE
  change ENNReal.ofReal (∫ γ, dist (γ 0) (γ 1) ^ 2 ∂π) ≤
    ENNReal.ofReal |0 - (t : ℝ)| ^ 2 * ENNReal.ofReal C at hcostE
  rw [zero_sub, abs_neg, abs_of_nonneg t.2.1,
    ← ENNReal.ofReal_pow t.2.1, ← ENNReal.ofReal_mul (sq_nonneg _)] at hcostE
  have hcost : (∫ γ, dist (γ 0) (γ 1) ^ 2 ∂π) ≤ (t : ℝ) ^ 2 * C := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcostE
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _),
      ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) hC)] using hh
  exact weighted_radial_rigidity_of_moments π p ht ht1 hπD
    (hi π 0 (hpbd 0 0 hπends.1)) (hi π 1 (hpbd 1 t hπends.2)) hcost hC0 hC1

end RegularPointCoordinates

end OAI
