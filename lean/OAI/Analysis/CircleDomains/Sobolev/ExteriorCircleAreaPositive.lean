import OAI.Analysis.CircleDomains.Sobolev.ExteriorCircleAreaContinuity
import OAI.Analysis.CircleDomains.Sobolev.PrincipalCircleAreaLimit

namespace OAI

/-! Principal normalization fixes the positive orientation of every
exterior image circle: signed area is continuous, never zero, and
positive on sufficiently large circles. -/
open Set Filter Function MeasureTheory Metric Bornology Asymptotics
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exterior_circle_area_eventually_pos {F : ℂ → ℂ} {R : ℝ}
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ᶠ a : ℝ in atTop, 0 < signedCurveArea (fun t => F (unitCircleParam 0 a t)) := by
  have hd : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with z hz
    exact (hF z hz).differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
  obtain ⟨c, T, hT, he⟩ := principal_exterior_expansion hd (principal_remainder_tendsto_zero hn)
  have hl := principal_circle_area_limit hT he
  have hsmall := hl.eventually (lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with a ha ha1
  have hs : (1 : ℝ) ≤ a^2 := one_le_pow₀ ha1
  have hp := Real.pi_gt_three
  nlinarith

lemma exterior_circle_area_pos (hsch : PlanarSchoenflies)
    (hgreen : UnorientedFiniteCircleGreenFormula) {F : ℂ → ℂ} {R a : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (hi : InjOn F {z | R < ‖z‖})
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) (ha : R < a) :
    0 < signedCurveArea (fun t => F (unitCircleParam 0 a t)) := by
  let A : ℝ → ℝ := fun r => signedCurveArea (fun t => F (unitCircleParam 0 r t))
  have hnz {r : ℝ} (hr : R < r) : A r ≠ 0 := by
    obtain ⟨H, hH, _⟩ := exterior_closed_core_jordan hsch hR hF hi hn hr
    exact regular_jordan_signed_area_ne_zero hgreen H _
      (exterior_image_circle_regular hR hF hi hr H hH)
  have hcont : ContinuousOn A (Ioi R) := exterior_circle_area_continuousOn hR hF
  obtain ⟨b, hb, hab⟩ := Filter.Eventually.exists
    ((exterior_circle_area_eventually_pos hF hn).and (eventually_ge_atTop a))
  change 0 < A b at hb
  change 0 < A a
  by_contra h
  have ha0 : A a ≤ 0 := le_of_not_gt h
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hab
    (hcont.mono (fun r hr => ha.trans_le hr.1)) (show (0 : ℝ) ∈ Icc (A a) (A b) from ⟨ha0, hb.le⟩)
  exact hnz (ha.trans_le hr.1) he

lemma exterior_jordan_area (hsch : PlanarSchoenflies)
    (hgreen : UnorientedFiniteCircleGreenFormula) {F : ℂ → ℂ} {R a : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (hi : InjOn F {z | R < ‖z‖})
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) (ha : R < a)
    (H : ℂ ≃ₜ ℂ)
    (hH : frontier (jordanInterior H) = range (fun z : Circle => F ((a : ℂ)*(z : ℂ)))) :
    (volume (jordanInterior H)).toReal = signedCurveArea (fun t => F (unitCircleParam 0 a t)) := by
  rw [← regular_jordan_signed_area hgreen H _ (exterior_image_circle_regular hR hF hi ha H hH),
    abs_of_pos (exterior_circle_area_pos hsch hgreen hR hF hi hn ha)]

end CircleDomainRigidity

end

end OAI
