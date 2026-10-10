import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ExpNegQuadraticBound

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
open Set Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma resolventHeat_second_error {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) :
    ‖(resolventHeat R t-1)*R^2-t • (R^2-R)‖ ≤ t^2/2 := by
  have hb : ‖cfc (fun s => (heatSymbol t s-1)*s^2-t*(s^2-s)) R‖ ≤ t^2/2 := by
    apply norm_cfc_le (by positivity)
    intro s hs
    exact heatSymbol_second_error ht (resolvent_spectrum_bounds hR hR1 hs)
  have hc1 : Continuous (fun s : ℝ => (heatSymbol t s-1)*s^2) :=
    ((heatSymbol_continuous t).sub continuous_const).mul (continuous_id.pow 2)
  have hc2 : Continuous (fun s : ℝ => s^2-s) := (continuous_id.pow 2).sub continuous_id
  have hid : cfc (fun s : ℝ => s) R = R := cfc_id ℝ R hR.isSelfAdjoint
  rw [cfc_sub _ _ R hc1.continuousOn (hc2.const_mul t).continuousOn,
    cfc_mul (fun s => heatSymbol t s-1) (fun s : ℝ => s^2) R
      ((heatSymbol_continuous t).sub continuous_const).continuousOn (continuous_id.pow 2).continuousOn,
    cfc_sub (heatSymbol t) (fun _ => 1) R (heatSymbol_continuous t).continuousOn continuous_const.continuousOn,
    cfc_const 1 R hR.isSelfAdjoint, map_one, cfc_pow_id R 2 hR.isSelfAdjoint,
    cfc_const_mul t (fun s : ℝ => s^2-s) R hc2.continuousOn,
    cfc_sub (fun s : ℝ => s^2) (fun s : ℝ => s) R (continuous_id.pow 2).continuousOn continuous_id.continuousOn,
    cfc_pow_id R 2 hR.isSelfAdjoint, hid] at hb
  exact hb

lemma resolventHeat_second_error_apply {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) (v : H) :
    ‖resolventHeat R t (R (R v))-R (R v)-t • (R (R v)-R v)‖ ≤ (t^2/2)*‖v‖ := by
  calc
    _ = ‖(((resolventHeat R t-1)*R^2-t • (R^2-R) : H →L[ℂ] H)) v‖ := rfl
    _ ≤ ‖(resolventHeat R t-1)*R^2-t • (R^2-R)‖*‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (resolventHeat_second_error hR hR1 ht) (norm_nonneg v)

lemma resolventHeat_slope_range2_error {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 < t) (v : H) :
    ‖t⁻¹ • (resolventHeat R t (R (R v))-R (R v))-(R (R v)-R v)‖ ≤ (t/2)*‖v‖ := by
  have he : t⁻¹ • (resolventHeat R t (R (R v))-R (R v))-(R (R v)-R v) =
      t⁻¹ • (resolventHeat R t (R (R v))-R (R v)-t • (R (R v)-R v)) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  calc
    _ ≤ t⁻¹*((t^2/2)*‖v‖) := mul_le_mul_of_nonneg_left
      (resolventHeat_second_error_apply hR hR1 ht.le v) (inv_nonneg.mpr ht.le)
    _ = (t/2)*‖v‖ := by field_simp

lemma resolventHeat_deriv_range2_zero {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) (v : H) :
    HasDerivWithinAt (fun t : ℝ => resolventHeat R t (R (R v)))
      (R (R v)-R v) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Ici (0:ℝ) \ {0} = Ioi 0 := by ext t; simp
  rw [hset, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (g := fun t : ℝ => (t/2)*‖v‖)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [slope_def_module, sub_zero, resolventHeat_zero hR,
      one_apply_eq_self] using resolventHeat_slope_range2_error hR hR1 ht v
  · have hcont : ContinuousAt (fun t : ℝ => (t/2)*‖v‖) 0 :=
      ((continuous_id.div_const 2).mul_const ‖v‖).continuousAt
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds

lemma positive_contraction_norm {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) : ‖R‖ ≤ 1 := by
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg R
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr hR)).mpr
    (ContinuousLinearMap.le_def.mpr hR1)

lemma resolventHeat_slope_range_contractive {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 < t) (u v : H) :
    dist (t⁻¹ • (resolventHeat R t (R u)-R u))
      (t⁻¹ • (resolventHeat R t (R v)-R v)) ≤ dist u v := by
  rw [dist_eq_norm, dist_eq_norm]
  have he : t⁻¹ • (resolventHeat R t (R u)-R u) -
      t⁻¹ • (resolventHeat R t (R v)-R v) =
      t⁻¹ • (resolventHeat R t (R (u-v))-R (u-v)) := by
    simp only [map_sub, smul_sub]
    abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  calc
    _ ≤ t⁻¹*(t*‖u-v‖) := mul_le_mul_of_nonneg_left
      (resolventHeat_range_error_apply hR hR1 ht.le (u-v)) (inv_nonneg.mpr ht.le)
    _ = ‖u-v‖ := by rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]

lemma resolvent_minus_id_bound {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) (u v : H) :
    dist (R u-u) (R v-v) ≤ 2*dist u v := by
  simp only [dist_eq_norm]
  have he : (R u-u)-(R v-v) = R (u-v)-(u-v) := by simp only [map_sub]; abel
  rw [he]
  calc
    _ ≤ ‖R (u-v)‖+‖u-v‖ := norm_sub_le _ _
    _ ≤ ‖R‖*‖u-v‖+‖u-v‖ := add_le_add (ContinuousLinearMap.le_opNorm R (u-v)) le_rfl
    _ ≤ 1*‖u-v‖+‖u-v‖ := by gcongr; exact positive_contraction_norm hR hR1
    _ = _ := by ring

lemma resolventHeat_slope_range_zero {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) (hd : R.toLinearMap.range.topologicalClosure = ⊤) (v : H) :
    Tendsto (fun t : ℝ => t⁻¹ • (resolventHeat R t (R v)-R v))
      (𝓝[>] (0:ℝ)) (𝓝 (R v-v)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hd' := Submodule.dense_iff_topologicalClosure_eq_top.mpr hd
  obtain ⟨u, hu, huR⟩ := Metric.dense_iff.mp hd' v (ε/8) (by positivity)
  obtain ⟨w,rfl⟩ := huR
  have hv : dist v (R w) < ε/8 := by simpa [dist_comm] using hu
  have htend : Tendsto (fun t : ℝ => (t/2)*‖w‖) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using ((((continuous_id.div_const 2).mul_const ‖w‖).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds : Tendsto (fun t : ℝ => (t/2)*‖w‖) (𝓝[>] (0:ℝ)) (𝓝 ((0/2)*‖w‖)))
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), (t/2)*‖w‖ < ε/2 :=
    (tendsto_order.1 htend).2 _ (by positivity)
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht ht0
  have hcon := resolventHeat_slope_range_contractive hR hR1 ht0 v (R w)
  have hn := resolventHeat_slope_range2_error hR hR1 ht0 w
  have hlim := resolvent_minus_id_bound hR hR1 (R w) v
  rw [dist_comm (R w) v] at hlim
  have htri := dist_triangle (t⁻¹ • (resolventHeat R t (R v)-R v))
    (t⁻¹ • (resolventHeat R t (R (R w))-R (R w))) (R v-v)
  have htri2 := dist_triangle (t⁻¹ • (resolventHeat R t (R (R w))-R (R w)))
    (R (R w)-R w) (R v-v)
  rw [dist_eq_norm (t⁻¹ • (resolventHeat R t (R (R w))-R (R w))) (R (R w)-R w)] at htri2
  linarith

lemma resolventHeat_deriv_range_zero {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) (hd : R.toLinearMap.range.topologicalClosure = ⊤) (v : H) :
    HasDerivWithinAt (fun t : ℝ => resolventHeat R t (R v))
      (R v-v) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Ici (0:ℝ) \ {0} = Ioi 0 := by ext t; simp
  rw [hset]
  change Tendsto (fun t => slope (fun s : ℝ => resolventHeat R s (R v)) 0 t)
    (𝓝[>] (0:ℝ)) (𝓝 (R v-v))
  simpa only [slope_def_module, sub_zero, resolventHeat_zero hR, one_apply_eq_self]
    using resolventHeat_slope_range_zero hR hR1 hd v

def heatInverseSymbol (t s : ℝ) : ℝ :=
  (Real.exp t / t) * ((s/t)⁻¹ * expNegInvGlue (s/t))

lemma heatInverseSymbol_continuous (t : ℝ) : Continuous (heatInverseSymbol t) := by
  have hc := expNegInvGlue.continuous_polynomial_eval_inv_mul (Polynomial.X : Polynomial ℝ)
  simp only [Polynomial.eval_X] at hc
  exact continuous_const.mul (hc.comp (continuous_id.div_const t))

lemma heatInverseSymbol_mul {t : ℝ} (ht : 0 < t) (s : ℝ) :
    s * heatInverseSymbol t s = heatSymbol t s := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp only [zero_mul, heatSymbol_nonpos ht le_rfl]
  · rw [heatInverseSymbol, heatSymbol, ite_eq_right ht.ne', inv_div]
    field_simp

lemma heatSymbol_maps_range {t : ℝ} (ht : 0 < t) (s : ℝ) :
    heatSymbol t s = s*heatInverseSymbol t s := (heatInverseSymbol_mul ht s).symm

lemma resolventHeat_eq_resolvent_mul {R : H →L[ℂ] H} (hR : R.IsPositive)
    {t : ℝ} (ht : 0 < t) :
    resolventHeat R t = R*cfc (heatInverseSymbol t) R := by
  have hid : cfc (fun s : ℝ => s) R = R := cfc_id ℝ R hR.isSelfAdjoint
  calc
    resolventHeat R t = cfc (fun s : ℝ => s*heatInverseSymbol t s) R :=
      cfc_congr fun s _ => heatSymbol_maps_range ht s
    _ = cfc (fun s : ℝ => s) R*cfc (heatInverseSymbol t) R :=
      cfc_mul _ _ _ continuous_id.continuousOn (heatInverseSymbol_continuous t).continuousOn
    _ = _ := by rw [hid]

lemma resolventHeat_mem_range {R : H →L[ℂ] H} (hR : R.IsPositive)
    {t : ℝ} (ht : 0 < t) (u : H) :
    resolventHeat R t u ∈ R.toLinearMap.range := by
  refine ⟨cfc (heatInverseSymbol t) R u, ?_⟩
  rw [resolventHeat_eq_resolvent_mul hR ht]
  rfl

lemma resolventHeat_commute_resolvent {R : H →L[ℂ] H} (hR : R.IsPositive) (t : ℝ) :
    Commute (resolventHeat R t) R := by
  have h := cfc_commute_cfc (heatSymbol t) (fun s : ℝ => s) R
  have hid : cfc (fun s : ℝ => s) R = R := cfc_id ℝ R hR.isSelfAdjoint
  rwa [hid] at h

lemma resolventHeat_resolvent {R : H →L[ℂ] H} (hR : R.IsPositive) (t : ℝ) (u : H) :
    resolventHeat R t (R u) = R (resolventHeat R t u) :=
  congrArg (fun T : H →L[ℂ] H => T u) (resolventHeat_commute_resolvent hR t).eq

end WeakHessianFunctional

end
end InlinedFile0

end OAI
