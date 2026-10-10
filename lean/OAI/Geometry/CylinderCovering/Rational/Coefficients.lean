import OAI.Geometry.CylinderCovering.Rational.CoefficientsDefinitions

namespace OAI

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

namespace RationalCoefficients

theorem ceiling_integral (alpha c0 c2 : ℝ) :
    (∫ y in (-(1/4:ℝ))..(1/4), alpha * (c0 + c2 * y^2) * y^2) =
      alpha * (c0 / 96 + c2 / 2560) := by
  have he : (fun y : ℝ => alpha * (c0 + c2 * y^2) * y^2) =
      (fun y => (alpha*c0)*y^2 + (alpha*c2)*y^4) := by
    funext y
    ring
  rw [he, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun y : ℝ => (alpha*c0)*y^2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun y : ℝ => (alpha*c2)*y^4)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  norm_num
  ring

theorem limiting_ceiling_integral :
    (∫ y in (-(1/4:ℝ))..(1/4), (y^2 / 16 + y^4)) = (1/960:ℝ) := by
  have h := ceiling_integral 1 (1/16) 1
  norm_num at h
  convert h using 1
  congr 1
  funext y
  ring

theorem limiting_angular_energy_integral :
    (∫ z in (-(1/2:ℝ))..(1/2),
      ((1/16 + z^2/4)^2 + (1/2)*(z/2)^2)) = (17/960:ℝ) := by
  have he : (fun z : ℝ => ((1/16 + z^2/4)^2 + (1/2)*(z/2)^2)) =
      (fun z => (1/256:ℝ) + (5/32)*z^2 + (1/16)*z^4) := by
    funext z
    ring
  rw [he, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun z : ℝ => (1/256:ℝ) + (5/32)*z^2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun z : ℝ => (1/16:ℝ)*z^4)).intervalIntegrable _ _),
    intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous (fun z : ℝ => (5/32:ℝ)*z^2)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  norm_num

theorem limiting_energy_integral :
    (1/2:ℝ) * (∫ r in (0:ℝ)..(1/2),
      r * (∫ z in (-(1/2:ℝ))..(1/2),
        ((1/16 + z^2/4)^2 + (1/2)*(z/2)^2))) = 17/15360 := by
  simp_rw [limiting_angular_energy_integral]
  rw [intervalIntegral.integral_mul_const]
  norm_num [integral_id]

theorem limiting_gap : (17/15360:ℝ) - 1/960 = 1/15360 := by norm_num

theorem angular_polynomial_integral (a b c : ℝ) :
    (∫ z in (-(1/2:ℝ))..(1/2), (a+b*z^2)^2 + (1/2)*(c*z)^2) =
      a^2 + (2*a*b+c^2/2)/12+b^2/80 := by
  have he : (fun z : ℝ => (a+b*z^2)^2 + (1/2)*(c*z)^2) =
      (fun z => a^2 + (2*a*b+c^2/2)*z^2 + b^2*z^4) := by
    funext z
    ring
  rw [he, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun z : ℝ => a^2 + (2*a*b+c^2/2)*z^2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun z : ℝ => b^2*z^4)).intervalIntegrable _ _),
    intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous (fun z : ℝ => (2*a*b+c^2/2)*z^2)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  norm_num
  ring

theorem angular_energy_integral (d r : ℝ) :
    (∫ z in (-(1/2:ℝ))..(1/2), angularEnergy d r z) =
      (angularA0 d r)^2 +
        (2*angularA0 d r*angularA2 d r+(angularB1 d r)^2/2)/12 +
        (angularA2 d r)^2/80 := by
  exact angular_polynomial_integral _ _ _

theorem angularA0_bounds {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) :
    0 ≤ angularA0 d r ∧ angularA0 d r ≤ 1/16 := by
  have hrd : 0 < r+d := by positivity
  have hden : 0 < 16*(r+d)^2 := by positivity
  constructor
  · unfold angularA0
    positivity
  · unfold angularA0
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg d]

theorem angularA2_bounds {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) :
    0 ≤ angularA2 d r ∧ angularA2 d r ≤ 1/4 := by
  have hrd : 0 < r+d := by positivity
  have hden : 0 < 4*(r+d)^2 := by positivity
  constructor
  · unfold angularA2
    positivity
  · unfold angularA2
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg d, mul_nonneg hr hd.le]

theorem angularB1_bounds {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) :
    0 ≤ angularB1 d r ∧ angularB1 d r ≤ 1/2 := by
  have hden : 0 < 2*(r+d) := by positivity
  constructor
  · unfold angularB1
    positivity
  · unfold angularB1
    apply (div_le_iff₀ hden).2
    linarith

theorem radialDensity_bounds {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r)
    (hr' : r ≤ 1/2) : 0 ≤ radialDensity d r ∧ radialDensity d r ≤ 1 := by
  obtain ⟨ha0, ha0'⟩ := angularA0_bounds hd hr
  obtain ⟨ha2, ha2'⟩ := angularA2_bounds hd hr
  obtain ⟨hb1, hb1'⟩ := angularB1_bounds hd hr
  have ha02 : (angularA0 d r)^2 ≤ (1/16:ℝ)^2 :=
    (sq_le_sq₀ ha0 (by norm_num)).2 ha0'
  have ha22 : (angularA2 d r)^2 ≤ (1/4:ℝ)^2 :=
    (sq_le_sq₀ ha2 (by norm_num)).2 ha2'
  have hb12 : (angularB1 d r)^2 ≤ (1/2:ℝ)^2 :=
    (sq_le_sq₀ hb1 (by norm_num)).2 hb1'
  have hprod : angularA0 d r * angularA2 d r ≤ (1/16:ℝ)*(1/4) :=
    mul_le_mul ha0' ha2' ha2 (by norm_num)
  have hnonneg : 0 ≤ (angularA0 d r)^2 +
      (2*angularA0 d r*angularA2 d r+(angularB1 d r)^2/2)/12 +
      (angularA2 d r)^2/80 := by positivity
  have hbound : (angularA0 d r)^2 +
      (2*angularA0 d r*angularA2 d r+(angularB1 d r)^2/2)/12 +
      (angularA2 d r)^2/80 ≤ 2 := by nlinarith
  unfold radialDensity
  constructor
  · exact mul_nonneg hr hnonneg
  · exact (mul_le_mul hr' hbound hnonneg (by norm_num)).trans (by norm_num)

theorem radialDensity_zero (d : ℝ) : radialDensity d 0 = 0 := by
  simp [radialDensity]

theorem radialDensity_limit {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun d => radialDensity d r) (𝓝[>] (0:ℝ)) (𝓝 (r*(17/960))) := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    simp only [radialDensity_zero, zero_mul]
    exact tendsto_const_nhds
  · have hr0 : r ≠ 0 := ne_of_gt hr
    have hc : ContinuousAt (fun d => radialDensity d r) 0 := by
      unfold radialDensity angularA0 angularA2 angularB1
      fun_prop (disch := positivity)
    have he : radialDensity 0 r = r*(17/960) := by
      unfold radialDensity angularA0 angularA2 angularB1
      field_simp
      ring
    rw [← he]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem radialDensity_measurable (d : ℝ) : Measurable (radialDensity d) := by
  unfold radialDensity angularA0 angularA2 angularB1
  fun_prop

theorem polarCost_eq (d : ℝ) :
    polarCost d = (1/2) * ∫ r in (0:ℝ)..(1/2), radialDensity d r := by
  unfold polarCost radialDensity
  simp_rw [angular_energy_integral]

theorem polarCost_limit :
    Tendsto polarCost (𝓝[>] (0:ℝ)) (𝓝 (17/15360:ℝ)) := by
  have hlim : Tendsto (fun d : ℝ => ∫ r in Ioc (0:ℝ) (1/2), radialDensity d r)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ r in Ioc (0:ℝ) (1/2), r*(17/960:ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ))
    · exact Filter.Eventually.of_forall (fun d => (radialDensity_measurable d).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with d hd
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      obtain ⟨h0,h1⟩ := radialDensity_bounds hd hr.1.le hr.2
      simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
    · exact integrableOn_const (by simp)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact radialDensity_limit hr.1.le
  have he : (∫ r in Ioc (0:ℝ) (1/2), r*(17/960:ℝ)) = 17/7680 := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2),
      intervalIntegral.integral_mul_const]
    norm_num [integral_id]
  have hm := (tendsto_const_nhds (x := (1/2:ℝ))).mul hlim
  convert hm using 1
  · ext d
    rw [polarCost_eq, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
  · rw [he]
    norm_num

theorem wedgeCost_eq_polarCost (d : ℝ) : wedgeCost d = polarCost d := by
  unfold wedgeCost polarCost
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  let f : ℝ → ℝ := fun y =>
    ((y^2/(4*(r+d)^2) + r*(r+2*d)/(16*(r+d)^2))^2 +
      (1/2)*(y/(2*(r+d)))^2)
  have hs := intervalIntegral.mul_integral_comp_mul_left
    (a := -(1/2:ℝ)) (b := 1/2) (f := f) r
  have hl : r * (-(1/2:ℝ)) = -r/2 := by ring
  have hu : r * (1/2:ℝ) = r/2 := by ring
  rw [hl, hu] at hs
  change (∫ y in (-r/2)..(r/2), f y) =
    r * ∫ z in (-(1/2:ℝ))..(1/2), angularEnergy d r z
  rw [← hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro z _
  dsimp [f, angularEnergy, angularA0, angularA2, angularB1]
  ring

theorem wedgeCost_limit :
    Tendsto wedgeCost (𝓝[>] (0:ℝ)) (𝓝 (17/15360:ℝ)) := by
  have he : wedgeCost = polarCost := funext wedgeCost_eq_polarCost
  rw [he]
  exact polarCost_limit

end RationalCoefficients

end

end OAI
