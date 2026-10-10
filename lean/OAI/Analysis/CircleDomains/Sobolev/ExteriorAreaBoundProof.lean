import OAI.Analysis.CircleDomains.Sobolev.ExteriorCircleAreaPositive
import OAI.Analysis.CircleDomains.Sobolev.ExteriorAnnulusArea
import OAI.Analysis.CircleDomains.Sobolev.ExteriorOmittedAreaInput

namespace OAI

/-! Discharge of the omitted-area form of the exterior area theorem.
The proof uses Green and Schoenflies, exact
annular energy, and the principal signed-area limit. -/
open Set Filter Function MeasureTheory Metric Bornology Asymptotics
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exterior_circle_area_le (hgreen : UnorientedFiniteCircleGreenFormula)
    {F : ℂ → ℂ} {R a : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) (ha : R < a) :
    signedCurveArea (fun t => F (unitCircleParam 0 a t)) ≤ Real.pi*a^2 := by
  have hd : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with z hz
    exact (hF z hz).differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
  obtain ⟨c, T, hT, he⟩ := principal_exterior_expansion hd (principal_remainder_tendsto_zero hn)
  have hlim := principal_circle_area_limit hT he
  have hle : ∀ᶠ b : ℝ in atTop,
      signedCurveArea (fun t => F (unitCircleParam 0 a t)) - Real.pi*a^2 ≤
        signedCurveArea (fun t => F (unitCircleParam 0 b t)) - Real.pi*b^2 := by
    filter_upwards [eventually_gt_atTop a] with b hab
    have henergy := exterior_annulus_energy hR hF (principal_remainder_tendsto_zero hn) ha hab.le
    have hint := exterior_annulus_energy_integrable hF ha (b := b)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall (fun z => sq_nonneg ‖deriv F z‖))] at henergy
    have hr := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun z => sq_nonneg ‖deriv F z‖))).mp henergy
    rw [← exterior_annulus_area hgreen hR hF ha hab] at hr
    nlinarith
  have hzero := ge_of_tendsto hlim hle
  linarith

lemma exteriorOmittedAreaTheorem (hsch : PlanarSchoenflies)
    (hgreen : UnorientedFiniteCircleGreenFormula) : ExteriorOmittedAreaTheorem := by
  intro F R hR hF hi hn
  have hext : (closedBall (0 : ℂ) R)ᶜ = {z : ℂ | R < ‖z‖} := by
    ext z
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le, mem_ofPred_eq]
  rw [hext] at hF hi
  unfold ExteriorOmittedAreaBound
  have hbound (a : ℝ) (ha : R < a) :
      volume ((F '' (closedBall (0 : ℂ) R)ᶜ)ᶜ) ≤ ENNReal.ofReal (Real.pi*a^2) := by
    obtain ⟨H, hH, hfill⟩ := exterior_closed_core_jordan hsch hR hF hi hn ha
    have hsub : ((F '' (closedBall (0 : ℂ) R)ᶜ)ᶜ) ⊆ jordanInterior H := by
      rw [← hfill]
      apply compl_subset_compl.mpr
      apply image_mono
      intro z hz
      rw [hext]
      exact ha.trans_le hz
    have hfin : volume (jordanInterior H) ≠ ∞ :=
      ((measure_mono subset_closure).trans_lt (isCompact_closure_jordanInterior H).measure_lt_top).ne
    calc
      _ ≤ volume (jordanInterior H) := measure_mono hsub
      _ = ENNReal.ofReal (signedCurveArea (fun t => F (unitCircleParam 0 a t))) := by
        rw [← exterior_jordan_area hsch hgreen hR hF hi hn ha H hH,
          ENNReal.ofReal_toReal hfin]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (exterior_circle_area_le hgreen hR hF hn ha)
  have ht : Tendsto (fun a : ℝ => ENNReal.ofReal (Real.pi*a^2)) (𝓝[>] R)
      (𝓝 (ENNReal.ofReal (Real.pi*R^2))) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_id.pow 2))).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact hbound a ha

end CircleDomainRigidity

end

end OAI
