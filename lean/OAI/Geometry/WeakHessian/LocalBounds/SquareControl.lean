import Mathlib
import OAI.Geometry.WeakHessian.Model

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace
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

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

def IsSquareControl (γ : Curve X) (a : ℝ → ℝ) : Prop :=
  Measurable a ∧ MemLp a 2 (volume.restrict (Icc (0:ℝ) 1)) ∧
    (∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), 0 ≤ a t) ∧
    ∀ s t : Time, (s:ℝ) ≤ (t:ℝ) →
      dist (γ s) (γ t) ≤ ∫ r in (s:ℝ)..(t:ℝ), a r

lemma IsSquareControl.intervalIntegrable {γ : Curve X} {a : ℝ → ℝ}
    (ha : IsSquareControl γ a) : IntervalIntegrable a volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  exact ha.2.1.integrable (by norm_num)

lemma evalReal_of_mem {γ : Curve X} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    evalReal γ t = γ ⟨t,ht⟩ := by
  change γ (clampTime t) = γ ⟨t,ht⟩
  apply congrArg γ
  apply Subtype.ext
  simp only [clampTime, max_eq_right ht.1, min_eq_right ht.2]

lemma IsSquareControl.dist_le_primitive {γ : Curve X} {a : ℝ → ℝ}
    (ha : IsSquareControl γ a) {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1)
    (ht : t ∈ Icc (0:ℝ) 1) :
    dist (evalReal γ s) (evalReal γ t) ≤
      |(∫ r in (0:ℝ)..s, a r) - ∫ r in (0:ℝ)..t, a r| := by
  have hInt (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : IntervalIntegrable a volume 0 r :=
    ha.intervalIntegrable.mono_set (by
      simpa only [uIcc_of_le zero_le_one, uIcc_of_le hr.1] using
        (Icc_subset_Icc le_rfl hr.2))
  have hdom (s t : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
      (hst : s ≤ t) : dist (evalReal γ s) (evalReal γ t) ≤
        (∫ r in (0:ℝ)..t, a r)-(∫ r in (0:ℝ)..s, a r) := by
    rw [evalReal_of_mem hs, evalReal_of_mem ht,
      intervalIntegral.integral_interval_sub_left (hInt t ht) (hInt s hs)]
    exact ha.2.2.2 ⟨s,hs⟩ ⟨t,ht⟩ hst
  rcases le_total s t with hst | hts
  · exact (hdom s t hs ht hst).trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · have H := hdom t s ht hs hts
    rw [dist_comm] at H
    exact H.trans (le_abs_self _)

lemma metricSpeed_le_of_deriv_control {γ : Curve X} {A : ℝ → ℝ} {v t : ℝ}
    (hA : HasDerivAt A v t)
    (hdom : ∀ᶠ s in 𝓝[≠] t, dist (evalReal γ s) (evalReal γ t) ≤ |A s-A t|) :
    metricSpeed γ t ≤ ENNReal.ofReal |v| := by
  have hlim : Tendsto (fun s => ENNReal.ofReal (|A s-A t| / |s-t|))
      (𝓝[≠] t) (𝓝 (ENNReal.ofReal |v|)) := by
    simpa only [slope, vsub_eq_sub, smul_eq_mul, norm_mul, norm_inv,
      Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using
      ENNReal.tendsto_ofReal (hasDerivAt_iff_tendsto_slope.mp hA).norm
  calc metricSpeed γ t
    _ ≤ limsup (fun s => ENNReal.ofReal (|A s-A t| / |s-t|)) (𝓝[≠] t) := by
      refine limsup_le_limsup ?_
      filter_upwards [hdom] with s hs
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hs (abs_nonneg _))
    _ = ENNReal.ofReal |v| := hlim.limsup_eq

lemma IsSquareControl.metricSpeed_le {γ : Curve X} {a : ℝ → ℝ}
    (ha : IsSquareControl γ a) :
    ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), metricSpeed γ t ≤ ENNReal.ofReal (a t) := by
  have hder := ha.intervalIntegrable.ae_hasDerivAt_integral
  have h0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have h1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_of_ae hder, ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae h0, ae_restrict_of_ae h1, ha.2.2.1] with t htder ht ht0 ht1 hta
  have hti : t ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  have H := metricSpeed_le_of_deriv_control
    (htder (by simpa only [uIcc_of_le zero_le_one] using ht) 0 (by simp))
    (show ∀ᶠ s in 𝓝[≠] t, dist (evalReal γ s) (evalReal γ t) ≤
      |(∫ r in (0:ℝ)..s, a r) - ∫ r in (0:ℝ)..t, a r| from by
      have hnear : ∀ᶠ s in 𝓝[≠] t, s ∈ Ioo (0:ℝ) 1 :=
        nhdsWithin_le_nhds (Ioo_mem_nhds hti.1 hti.2)
      filter_upwards [hnear] with s hs
      exact ha.dist_le_primitive ⟨hs.1.le,hs.2.le⟩ ht)
  simpa only [abs_of_nonneg hta] using H

lemma IsSquareControl.isAC2 {γ : Curve X} {a : ℝ → ℝ}
    (ha : IsSquareControl γ a) : IsAC2 γ := by
  refine ⟨fun t => ENNReal.ofReal (a t), ENNReal.measurable_ofReal.comp ha.1, ?_, ?_⟩
  · have H := ha.2.1.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      ha.2.1.aestronglyMeasurable] at H
    simp only [ENNReal.toReal_ofNat, one_div] at H
    have Hfin : (∫⁻ t in Icc (0:ℝ) 1, ‖a t‖ₑ ^ (2:ℝ)) < ∞ := by
      exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < (2:ℝ)⁻¹)).mp H
    apply lt_of_le_of_lt _ Hfin
    apply lintegral_mono
    intro t
    change (ENNReal.ofReal (a t))^2 ≤ ‖a t‖ₑ ^ (2:ℝ)
    rw [ENNReal.rpow_two]
    exact pow_le_pow_left₀ (by positivity) (by
      simpa only [← ofReal_norm, Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal (le_abs_self (a t))) 2
  · intro s t hst
    have hsub : Icc (s:ℝ) (t:ℝ) ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc s.2.1 t.2.2
    have hint := (ha.2.1.integrable (by norm_num)).mono_measure (Measure.restrict_mono hsub le_rfl)
    have hnon := ae_mono (Measure.restrict_mono hsub le_rfl) ha.2.2.1
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnon,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hst]
    simpa only [edist_dist] using ENNReal.ofReal_le_ofReal (ha.2.2.2 s t hst)

end WeakHessian

open Set Filter Topology Bornology
open scoped InnerProductSpace

end
end InlinedFile0

end OAI
