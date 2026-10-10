import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SpeedApprox
import OAI.Geometry.WeakHessian.LocalBounds.AffineTime

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma IsTestPlan.restrictCurve {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (a b : Time) (hab : (a : ℝ) < b) :
    IsTestPlan m (Measure.map (WeakHessian.restrictCurve a b) π) := by
  let : IsProbabilityMeasure π := hπ.1
  have hr := continuous_restrictCurve (X := X) a b
  obtain ⟨C, hC⟩ := hπ.2.1
  refine ⟨inferInstance,
    ⟨C, fun t => ?_⟩, ?_, ?_⟩
  · rw [Measure.map_map (continuous_eval_const t).measurable hr.measurable]
    exact hC (affineTime a b t)
  · apply continuous_ae_map_of_ae hr
    filter_upwards [hπ.2.2.1] with γ hγ
    exact hγ.restrictCurve a b hab
  · rw [lintegral_map (measurable_metricSpeed.pow_const 2).lintegral_prod_right hr.measurable]
    calc
      (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed (WeakHessian.restrictCurve a b γ) t ^ 2 ∂volume ∂π) =
          ENNReal.ofReal ((b : ℝ) - a) *
            ∫⁻ γ, ∫⁻ t in Set.Icc (a : ℝ) b, metricSpeed γ t ^ 2 ∂volume ∂π := by
        simp_rw [kineticEnergy_restrictCurve a b hab]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((b : ℝ) - a) *
            ∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed γ t ^ 2 ∂volume ∂π := by
        gcongr 1
        exact lintegral_mono fun γ =>
          lintegral_mono_set (Set.Icc_subset_Icc a.property.1 b.property.2)
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hπ.2.2.2

omit [MeasurableSpace X] [BorelSpace X] in
lemma BoundedTracks.restrictCurve {π : Measure (Curve X)} [IsFiniteMeasure π]
    (hb : BoundedTracks π) (a b : Time) :
    BoundedTracks (Measure.map (WeakHessian.restrictCurve a b) π) := by
  obtain ⟨o, R, hR, hb⟩ := hb
  refine ⟨o, R, hR, continuous_ae_map_of_ae (continuous_restrictCurve a b) ?_⟩
  filter_upwards [hb] with γ hγ
  exact fun t => hγ (affineTime a b t)

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma action_restrictCurve (D : X → ℝ) (a b : Time) (hab : (a : ℝ) < b) (γ : Curve X) :
    (∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (D (evalReal (restrictCurve a b γ) t)) * metricSpeed (restrictCurve a b γ) t) =
    ∫⁻ t in Set.Icc (a : ℝ) b, ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  have heq : (fun t => ENNReal.ofReal (D (evalReal (restrictCurve a b γ) t)) *
      metricSpeed (restrictCurve a b γ) t) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun t => ENNReal.ofReal ((b : ℝ) - a) *
        (ENNReal.ofReal (D (evalReal γ ((a : ℝ) + ((b : ℝ) - a) * t))) *
          metricSpeed γ ((a : ℝ) + ((b : ℝ) - a) * t))) := by
    filter_upwards [ae_metricSpeed_restrictCurve a b hab γ, ae_restrict_mem measurableSet_Icc]
      with t ht hm
    rw [ht, evalReal_restrictCurve hm]
    ac_rfl
  rw [lintegral_congr_ae heq,
    lintegral_scaled_affine_Icc (a : ℝ) ((b : ℝ) - a) (sub_pos.mpr hab) 0 1
      (fun t => ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t)]
  rw [show (a : ℝ) + ((b : ℝ) - a) * 0 = a by ring,
    show (a : ℝ) + ((b : ℝ) - a) * 1 = b by ring]

lemma IsLocalWeakUpperGradient.ae_subinterval_le {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (a b : Time) (hab : (a : ℝ) < b) :
    ∀ᵐ γ ∂π, ENNReal.ofReal |f (γ b) - f (γ a)| ≤
      ∫⁻ t in Set.Icc (a : ℝ) b, ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  let : IsProbabilityMeasure π := hπ.1
  have ht := hD.ae_endpoint_le hf (hπ.restrictCurve a b hab) (hb.restrictCurve a b)
  have hh := ae_of_ae_map (continuous_restrictCurve a b).measurable.aemeasurable ht
  filter_upwards [hh] with γ hγ
  simpa only [restrictCurve_zero, restrictCurve_one, action_restrictCurve D a b hab γ] using hγ

end WeakHessian

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma IsTestPlan.lintegral_eval_le {π : Measure (Curve X)} (_hπ : IsTestPlan m π)
    {C : ℝ≥0} (hC : ∀ t : Time, Measure.map (fun γ : Curve X => γ t) π ≤ (C : ℝ≥0∞) • m)
    {q : X → ℝ≥0∞} (hq : AEMeasurable q m) (t : Time) :
    (∫⁻ γ, q (γ t) ∂π) ≤ (C : ℝ≥0∞) * ∫⁻ x, q x ∂m := by
  have hqm := hq.mono_ac (Measure.absolutelyContinuous_of_le_smul (hC t))
  rw [← lintegral_map' hqm (continuous_eval_const t).measurable.aemeasurable]
  calc
    (∫⁻ x, q x ∂Measure.map (fun γ : Curve X => γ t) π) ≤
        ∫⁻ x, q x ∂(C : ℝ≥0∞) • m := lintegral_mono' (hC t) le_rfl
    _ = _ := lintegral_smul_measure _ _

lemma IsTestPlan.lintegral_square_eval_lt_top {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π) {D : X → ℝ} (hD : LocallyL2 m D) :
    (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((D (evalReal γ t)) ^ 2) ∂volume ∂π) < ∞ := by
  let : IsProbabilityMeasure π := hπ.1
  obtain ⟨o, R, hR, hbound⟩ := hb
  obtain ⟨C, hC⟩ := hπ.2.1
  let q : X → ℝ≥0∞ := (Metric.ball o (R+1)).indicator (fun x => ENNReal.ofReal (D x ^ 2))
  have hqm : AEMeasurable q m :=
    (hD.aemeasurable.pow_const 2).ennreal_ofReal.indicator measurableSet_ball
  have hqfinite : (∫⁻ x, q x ∂m) < ∞ := by
    dsimp only [q]
    rw [lintegral_indicator measurableSet_ball]
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg (D x))).mp
      (hD o (R+1) (by linarith)).integrable_sq.hasFiniteIntegral
  have hstep : ∀ t : ℝ,
      (∫⁻ γ, ENNReal.ofReal ((D (evalReal γ t)) ^ 2) ∂π) ≤
        (C : ℝ≥0∞) * ∫⁻ x, q x ∂m := by
    intro t
    have heq : (fun γ : Curve X => ENNReal.ofReal ((D (evalReal γ t)) ^ 2)) =ᵐ[π]
        (fun γ => q (evalReal γ t)) := by
      filter_upwards [hbound] with γ hγ
      have hmem : evalReal γ t ∈ Metric.ball o (R+1) := (hγ (clampTime t)).trans_lt (by linarith)
      change _ = (Metric.ball o (R+1)).indicator (fun x => ENNReal.ofReal (D x ^ 2)) (evalReal γ t)
      exact (Set.indicator_of_mem hmem (fun x : X => ENNReal.ofReal (D x ^ 2))).symm
    rw [lintegral_congr_ae heq]
    exact hπ.lintegral_eval_le hC hqm (clampTime t)
  have hm : AEMeasurable (fun z : Curve X × ℝ => ENNReal.ofReal (D (evalReal z.1 z.2) ^ 2))
      (π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    ((hπ.aemeasurable_evalReal hD.aemeasurable).pow_const 2).ennreal_ofReal
  rw [lintegral_lintegral_swap hm]
  calc
    (∫⁻ t in Set.Icc (0 : ℝ) 1, ∫⁻ γ, ENNReal.ofReal ((D (evalReal γ t)) ^ 2) ∂π) ≤
        ∫⁻ t in Set.Icc (0 : ℝ) 1, (C : ℝ≥0∞) * ∫⁻ x, q x ∂m := lintegral_mono hstep
    _ = (C : ℝ≥0∞) * ∫⁻ x, q x ∂m := by simp
    _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top hqfinite

omit [MeasurableSpace X] [BorelSpace X] in
lemma ofReal_sq_le_ofReal_sq (x : ℝ) : ENNReal.ofReal x ^ 2 ≤ ENNReal.ofReal (x ^ 2) := by
  by_cases hx : 0 ≤ x
  · rw [ENNReal.ofReal_pow hx]
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hx), zero_pow (by norm_num : 2 ≠ 0)]
    exact bot_le

lemma IsTestPlan.lintegral_action_lt_top {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π) {D : X → ℝ} (hD : LocallyL2 m D) :
    (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t ∂volume ∂π) < ∞ := by
  let : IsProbabilityMeasure π := hπ.1
  let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hmul : ∀ u v : ℝ≥0∞, u*v ≤ u^2+v^2 := by
    intro u v
    rcases le_total u v with h|h
    · calc
        u*v ≤ v*v := mul_le_mul_left h v
        _ ≤ u^2+v^2 := by simp only [pow_two]; exact le_add_left le_rfl
    · calc
        u*v ≤ u*u := mul_le_mul_right h u
        _ ≤ u^2+v^2 := by simp only [pow_two]; exact le_add_right le_rfl
  have hsq : ∀ z : Curve X × ℝ,
      ENNReal.ofReal (D (evalReal z.1 z.2)) * metricSpeed z.1 z.2 ≤
        ENNReal.ofReal (D (evalReal z.1 z.2) ^ 2) + metricSpeed z.1 z.2 ^ 2 := by
    intro z
    exact (hmul _ _).trans (add_le_add_left (ofReal_sq_le_ofReal_sq _) _)
  have hmD := ((hπ.aemeasurable_evalReal hD.aemeasurable).pow_const 2).ennreal_ofReal
  rw [← lintegral_prod _ (hπ.aemeasurable_action hD)]
  calc
    (∫⁻ z, ENNReal.ofReal (D (evalReal z.1 z.2)) * metricSpeed z.1 z.2 ∂π.prod ν) ≤
        ∫⁻ z, ENNReal.ofReal (D (evalReal z.1 z.2) ^ 2) + metricSpeed z.1 z.2 ^ 2 ∂π.prod ν :=
      lintegral_mono hsq
    _ = (∫⁻ z, ENNReal.ofReal (D (evalReal z.1 z.2) ^ 2) ∂π.prod ν) +
        ∫⁻ z, metricSpeed z.1 z.2 ^ 2 ∂π.prod ν := lintegral_add_left' hmD _
    _ = (∫⁻ γ, ∫⁻ t, ENNReal.ofReal ((D (evalReal γ t)) ^ 2) ∂ν ∂π) +
        ∫⁻ γ, ∫⁻ t, metricSpeed γ t ^ 2 ∂ν ∂π := by
      rw [lintegral_prod _ hmD, lintegral_prod _ (measurable_metricSpeed.pow_const 2).aemeasurable]
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hπ.lintegral_square_eval_lt_top hb hD, hπ.2.2.2⟩

end WeakHessian

end
end InlinedFile0

end OAI
