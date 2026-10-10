import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarSharpDecay
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarModeDerivatives

namespace OAI

/-! The same sharp exponential rate for compact forcing derivatives. The
heat-kernel proof is applied to the actual first/second derivative forcing,
without assuming differentiated resolvent asymptotics. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarResolventOf_product_integrable {g : PlanarPosition → ℝ} {B : ℝ}
    (hg : Continuous g) (hB : ∀ x, ‖g x‖ ≤ B) (r : PlanarPosition) :
    Integrable (fun p : ℝ × PlanarPosition => planarResolventIntegrand p * g (r - p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure PlanarPosition)) := by
  apply planarResolventIntegrand_integrable.mul_bdd (c := B)
    ((hg.comp (continuous_const.sub continuous_snd)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun p => hB (r - p.2))

theorem planarResolventOf_bounded_heat_representation {g : PlanarPosition → ℝ} {B : ℝ}
    (hg : Continuous g) (hB : ∀ x, ‖g x‖ ≤ B) (r : PlanarPosition) :
    planarResolventOf g r = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) *
      (∫ b, planarHeatKernel t b * g (r - b)) := by
  unfold planarResolventOf planarResolventKernel
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (planarResolventOf_product_integrable hg hB r)]
  simp_rw [planarResolventIntegrand, mul_assoc, integral_const_mul]

theorem planar_supported_exponential_bound {g : PlanarPosition → ℝ} {B : ℝ}
    (hs : tsupport g ⊆ Metric.closedBall 0 1) (hB : ∀ x, ‖g x‖ ≤ B)
    (e s : PlanarPosition) : ‖g s‖ ≤ B * Real.exp (‖e‖ - inner ℝ e s) := by
  have hB₀ : 0 ≤ B := (norm_nonneg (g 0)).trans (hB 0)
  by_cases hg : g s = 0
  · rw [hg, norm_zero]
    exact mul_nonneg hB₀ (Real.exp_pos _).le
  have hsn : ‖s‖ ≤ 1 := by
    have h := hs (subset_tsupport g hg)
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  have hi : inner ℝ e s ≤ ‖e‖ := (real_inner_le_norm e s).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsn (norm_nonneg e))
  exact (hB s).trans (le_mul_of_one_le_right hB₀ (Real.one_le_exp (by linarith)))

theorem planarHeatOf_tilt_bound {g : PlanarPosition → ℝ} {B t : ℝ}
    (hs : tsupport g ⊆ Metric.closedBall 0 1) (hB : ∀ x, ‖g x‖ ≤ B)
    (ht : 0 < t) (e r : PlanarPosition) :
    ‖∫ b, planarHeatKernel t b * g (r - b)‖ ≤
      (B * Real.exp (‖e‖ - inner ℝ e r)) * Real.exp (t * ‖e‖ ^ 2) := by
  have hpt (b : PlanarPosition) : ‖planarHeatKernel t b * g (r - b)‖ ≤
      ((B * Real.exp (‖e‖ - inner ℝ e r)) * Real.exp (t * ‖e‖ ^ 2)) *
        planarHeatKernel t (b - (2 * t) • e) := by
    rw [norm_mul, Real.norm_of_nonneg (planarHeatKernel_positive ht b).le]
    calc
      _ ≤ planarHeatKernel t b * (B * Real.exp (‖e‖ - inner ℝ e (r - b))) :=
        mul_le_mul_of_nonneg_left (planar_supported_exponential_bound hs hB e (r - b))
          (planarHeatKernel_positive ht b).le
      _ = (B * Real.exp (‖e‖ - inner ℝ e r)) *
          (planarHeatKernel t b * Real.exp (inner ℝ e b)) := by
        rw [inner_sub_right, show ‖e‖ - (inner ℝ e r - inner ℝ e b) =
          (‖e‖ - inner ℝ e r) + inner ℝ e b by ring, Real.exp_add]
        ring
      _ = _ := by rw [planarHeatKernel_tilt ht]; ring
  have h := norm_integral_le_of_norm_le
    (((planarHeatKernel_integrable ht).comp_sub_right ((2 * t) • e)).const_mul
      ((B * Real.exp (‖e‖ - inner ℝ e r)) * Real.exp (t * ‖e‖ ^ 2)))
    (Filter.Eventually.of_forall hpt)
  simpa only [integral_const_mul, integral_sub_right_eq_self, planarHeatKernel_integral ht,
    mul_one] using h

theorem planarResolventOf_tilt_bound {g : PlanarPosition → ℝ} {B : ℝ}
    (hg : Continuous g) (hs : tsupport g ⊆ Metric.closedBall 0 1) (hB : ∀ x, ‖g x‖ ≤ B)
    (e r : PlanarPosition) (he : ‖e‖ < 1) :
    ‖planarResolventOf g r‖ ≤ B * Real.exp (‖e‖ - inner ℝ e r) / (1 - ‖e‖ ^ 2) := by
  have hc : 0 < 1 - ‖e‖ ^ 2 := by nlinarith [norm_nonneg e]
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(1 - ‖e‖ ^ 2) * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hc
  rw [planarResolventOf_bounded_heat_representation hg hB r]
  have h := norm_integral_le_of_norm_le
    (f := fun t : ℝ => Real.exp (-t) * (∫ b, planarHeatKernel t b * g (r - b)))
    (hi.const_mul (B * Real.exp (‖e‖ - inner ℝ e r))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc
        _ ≤ Real.exp (-t) * ((B * Real.exp (‖e‖ - inner ℝ e r)) * Real.exp (t * ‖e‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (planarHeatOf_tilt_bound hs hB ht e r) (Real.exp_pos _).le
        _ = (B * Real.exp (‖e‖ - inner ℝ e r)) * Real.exp (-(1 - ‖e‖ ^ 2) * t) := by
          rw [show -(1 - ‖e‖ ^ 2) * t = -t + t * ‖e‖ ^ 2 by ring, Real.exp_add]
          ring)
  have heval : (∫ t : ℝ in Set.Ioi 0, Real.exp (-(1 - ‖e‖ ^ 2) * t)) =
      (1 - ‖e‖ ^ 2)⁻¹ := by
    rw [integral_exp_mul_Ioi (by linarith : -(1 - ‖e‖ ^ 2) < 0)]
    simp
    rw [show ‖e‖ ^ 2 - 1 = -(1 - ‖e‖ ^ 2) by ring, div_neg]
    simp only [neg_div, neg_neg, one_div]
  simpa only [integral_const_mul, heval, div_eq_mul_inv] using h

theorem planarResolventOf_sharp_upper {g : PlanarPosition → ℝ} {B : ℝ}
    (hg : Continuous g) (hs : tsupport g ⊆ Metric.closedBall 0 1) (hB : ∀ x, ‖g x‖ ≤ B)
    {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    ‖planarResolventOf g r‖ ≤ B * ‖r‖ * Real.exp (2 - ‖r‖) := by
  have hB₀ : 0 ≤ B := (norm_nonneg (g 0)).trans (hB 0)
  by_cases hBzero : B = 0
  · simpa only [hBzero, zero_mul] using planarResolventOf_bound hB r
  have hBpos : 0 < B := lt_of_le_of_ne hB₀ (Ne.symm hBzero)
  have h := planar_tilt_envelope_sharp_upper r (‖planarResolventOf g r‖ / B)
    (fun e he => (div_le_iff₀ hBpos).2
      ((planarResolventOf_tilt_bound hg hs hB e r he).trans_eq (by ring))) hr
  have hh := (div_le_iff₀ hBpos).mp h
  convert hh using 1; ring

theorem planarResolventMode_partial_sharp_tail (e : PlanarPosition) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : PlanarPosition, 1 ≤ ‖r‖ →
      ‖planarPartial planarResolventMode e r‖ ≤ B * ‖r‖ * Real.exp (2 - ‖r‖) := by
  have hg := planarPartial_continuous (planarForcing_C7.of_le (by norm_num)) e
  have hc := planarForcing_hasCompactSupport.fderiv_apply ℝ e
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  refine ⟨B, (norm_nonneg _).trans (hB 0), fun r hr => ?_⟩
  rw [planarResolventMode_partial]
  exact planarResolventOf_sharp_upper hg
    ((tsupport_fderiv_apply_subset ℝ e).trans planarForcing_support) hB hr

theorem planarResolventMode_partial_partial_sharp_tail (e v : PlanarPosition) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : PlanarPosition, 1 ≤ ‖r‖ →
      ‖planarPartial (planarPartial planarResolventMode e) v r‖ ≤
        B * ‖r‖ * Real.exp (2 - ‖r‖) := by
  have hg := planarPartial_continuous (planarPartial_C1 (planarForcing_C7.of_le (by norm_num)) e) v
  have hc := (planarForcing_hasCompactSupport.fderiv_apply ℝ e).fderiv_apply ℝ v
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  refine ⟨B, (norm_nonneg _).trans (hB 0), fun r hr => ?_⟩
  rw [planarResolventMode_partial_partial]
  exact planarResolventOf_sharp_upper hg
    ((tsupport_fderiv_apply_subset ℝ v).trans
      ((tsupport_fderiv_apply_subset ℝ e).trans planarForcing_support)) hB hr

end ContinuumCoulomb

end

end OAI
