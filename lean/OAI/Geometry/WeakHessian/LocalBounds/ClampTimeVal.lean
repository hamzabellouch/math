import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.JoinCurve
import OAI.Geometry.WeakHessian.Transport.JoinControl

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
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal

namespace WeakHessian
open WeakHessianTransport

variable {X : Type*} [MetricSpace X]

lemma clampTime_val_eq {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) : (clampTime r : ℝ) = r := by
  simp only [clampTime, min_eq_right hr.2, max_eq_right hr.1]

lemma hasControlBound_of_memLp {γ : Curve X} {a : ℝ → ℝ}
    (ha : MemLp a 2 timeMeasure)
    (hd : ∀ s t : Time, s ≤ t → dist (γ s) (γ t) ≤ ∫ r in (s:ℝ)..(t:ℝ), a r) :
    HasControlBound γ (Real.sqrt (∫ r in Icc (0:ℝ) 1, (a r)^2)) := by
  let u := ha.toLp a
  have hueq : u =ᵐ[timeMeasure] a := MemLp.coeFn_toLp ha
  have hn : ‖u‖^2 = ∫ r in Icc (0:ℝ) 1, (a r)^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hueq] with r hr
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hr]
  refine ⟨u, ?_, fun s t hst => ?_⟩
  · rw [← hn, Real.sqrt_sq (norm_nonneg u)]
  · rw [intervalFunctional_apply s t u hst]
    have heq : (∫ r in (s:ℝ)..(t:ℝ), u r) = ∫ r in (s:ℝ)..(t:ℝ), a r := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le (show (s:ℝ) ≤ (t:ℝ) from hst)]
      exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Icc_self.trans (Icc_subset_Icc s.2.1 t.2.2)) hueq
    rw [heq]
    exact hd s t hst

lemma join_distance_integral {γ η : Curve X} (h : γ timeOne = η timeZero)
    {a b : ℝ → ℝ} (ha : IsSquareControl γ a) (hb : IsSquareControl η b) :
    ∀ s t : Time, s ≤ t → dist (joinCurve γ η h s) (joinCurve γ η h t) ≤
      ∫ r in (s:ℝ)..(t:ℝ), joinControl a b r := by
  have haI : IntervalIntegrable a volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr (ha.2.1.integrable (by norm_num))
  have hbI : IntervalIntegrable b volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr (hb.2.1.integrable (by norm_num))
  have hjI := intervalIntegrable_joinControl haI hbI
  have HL (s t : Time) (hst : s ≤ t) (ht : (t:ℝ) ≤ 1/2) :
      dist (joinCurve γ η h s) (joinCurve γ η h t) ≤ ∫ r in (s:ℝ)..(t:ℝ), joinControl a b r := by
    have hs : (s:ℝ) ≤ 1/2 := (show (s:ℝ) ≤ (t:ℝ) from hst).trans ht
    have hsc : 2*(s:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by have := s.2.1; linarith, by linarith⟩
    have htc : 2*(t:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by have := t.2.1; linarith, by linarith⟩
    rw [joinCurve_apply_left _ _ _ s hs, joinCurve_apply_left _ _ _ t ht,
      integral_joinControl_left _ _ hst ht]
    have H := ha.2.2.2 (clampTime (2*(s:ℝ))) (clampTime (2*(t:ℝ))) (by
      rw [clampTime_val_eq hsc, clampTime_val_eq htc]
      linarith [show (s:ℝ) ≤ (t:ℝ) from hst])
    simpa only [evalReal, clampTime_val_eq hsc, clampTime_val_eq htc] using H
  have HR (s t : Time) (hst : s ≤ t) (hs : 1/2 ≤ (s:ℝ)) :
      dist (joinCurve γ η h s) (joinCurve γ η h t) ≤ ∫ r in (s:ℝ)..(t:ℝ), joinControl a b r := by
    have ht : 1/2 ≤ (t:ℝ) := hs.trans (show (s:ℝ) ≤ (t:ℝ) from hst)
    have hsc : 2*(s:ℝ)-1 ∈ Icc (0:ℝ) 1 := ⟨by linarith, by have := s.2.2; linarith⟩
    have htc : 2*(t:ℝ)-1 ∈ Icc (0:ℝ) 1 := ⟨by linarith, by have := t.2.2; linarith⟩
    rw [joinCurve_apply_right _ _ _ s hs, joinCurve_apply_right _ _ _ t ht,
      integral_joinControl_right _ _ hst hs]
    have H := hb.2.2.2 (clampTime (2*(s:ℝ)-1)) (clampTime (2*(t:ℝ)-1)) (by
      rw [clampTime_val_eq hsc, clampTime_val_eq htc]
      linarith [show (s:ℝ) ≤ (t:ℝ) from hst])
    simpa only [evalReal, clampTime_val_eq hsc, clampTime_val_eq htc] using H
  intro s t hst
  by_cases ht : (t:ℝ) ≤ 1/2
  · exact HL s t hst ht
  by_cases hs : 1/2 ≤ (s:ℝ)
  · exact HR s t hst hs
  let m : Time := ⟨1/2, by norm_num, by norm_num⟩
  have hsm : s ≤ m := le_of_lt (lt_of_not_ge hs)
  have hmt : m ≤ t := le_of_lt (lt_of_not_ge ht)
  calc
    dist (joinCurve γ η h s) (joinCurve γ η h t) ≤
        dist (joinCurve γ η h s) (joinCurve γ η h m)+dist (joinCurve γ η h m) (joinCurve γ η h t) := dist_triangle _ _ _
    _ ≤ (∫ r in (s:ℝ)..(m:ℝ), joinControl a b r)+(∫ r in (m:ℝ)..(t:ℝ), joinControl a b r) :=
      add_le_add (HL s m hsm le_rfl) (HR m t hmt le_rfl)
    _ = _ := intervalIntegral.integral_add_adjacent_intervals
      (hjI.mono_set (uIcc_subset_uIcc (by simpa only [uIcc_of_le zero_le_one] using s.2)
        (by simpa only [uIcc_of_le zero_le_one] using m.2)))
      (hjI.mono_set (uIcc_subset_uIcc (by simpa only [uIcc_of_le zero_le_one] using m.2)
        (by simpa only [uIcc_of_le zero_le_one] using t.2)))

lemma hasControlBound_join {γ η : Curve X} (h : γ timeOne = η timeZero)
    {A B : ℝ} (hA : HasControlBound γ A) (hB : HasControlBound η B) :
    HasControlBound (joinCurve γ η h) (Real.sqrt (2*(A^2+B^2))) := by
  obtain ⟨a,ha,haA⟩ := hA.squareControl
  obtain ⟨b,hb,hbB⟩ := hB.squareControl
  have haI : IntervalIntegrable (fun r => (a r)^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr ha.2.1.integrable_sq
  have hbI : IntervalIntegrable (fun r => (b r)^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hb.2.1.integrable_sq
  have hj : MemLp (joinControl a b) 2 timeMeasure :=
    (memLp_two_iff_integrable_sq (measurable_joinControl ha.1 hb.1).aestronglyMeasurable).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
        (intervalIntegrable_joinControl_sq haI hbI))
  have H := hasControlBound_of_memLp hj (join_distance_integral h ha hb)
  obtain ⟨u,hu,hud⟩ := H
  refine ⟨u,hu.trans ?_,hud⟩
  apply Real.sqrt_le_sqrt
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_joinControl_sq haI hbI]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one] at haA hbB
  linarith

end WeakHessian

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal

end
end InlinedFile0

end OAI
