import OAI.Analysis.CircleDomains.Sobolev.ScalarEnergyMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! The actual scalar map flattening an open set of prescribed values.
It is one-Lipschitz, stays uniformly close to the identity, and is locally
constant on the open set, even when that open set is dense. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal Interval
noncomputable section
namespace CircleDomainRigidity

 def flattenValues (O : Set ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Oᶜ.indicator (fun _ => (1 : ℝ)) s

 theorem flattenValues_integrable {O : Set ℝ} (hO : MeasurableSet O) (a b : ℝ) :
    IntervalIntegrable (Oᶜ.indicator (fun _ => (1 : ℝ))) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b).mono_fun
    ((measurable_const.indicator hO.compl).aestronglyMeasurable)
  exact Eventually.of_forall fun s => by by_cases hs : s ∈ O <;> simp [hs]

 theorem flattenValues_sub {O : Set ℝ} (hO : MeasurableSet O) (a b : ℝ) :
    flattenValues O b - flattenValues O a =
      ∫ s in a..b, Oᶜ.indicator (fun _ => (1 : ℝ)) s := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (flattenValues_integrable hO 0 a) (flattenValues_integrable hO a b)
  dsimp only [flattenValues]
  linarith

 theorem flattenValues_lipschitz {O : Set ℝ} (hO : MeasurableSet O) :
    LipschitzWith 1 (flattenValues O) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  rw [flattenValues_sub hO]
  simpa only [Real.norm_eq_abs, one_mul] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (f := Oᶜ.indicator (fun _ => (1 : ℝ))) (a := b) (b := a) (C := 1) (fun s _ => by by_cases hs : s ∈ O <;> simp [hs]))

 theorem flattenValues_locally_constant {O : Set ℝ} (hO : IsOpen O) {x : ℝ} (hx : x ∈ O) :
    ∃ U ∈ 𝓝 x, EqOn (flattenValues O) (fun _ => flattenValues O x) U := by
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hO.mem_nhds hx)
  refine ⟨Ioo a b, Ioo_mem_nhds hax hxb, ?_⟩
  intro y hy
  have hzero : (∫ s in x..y, Oᶜ.indicator (fun _ => (1 : ℝ)) s) = 0 := by
    apply intervalIntegral.integral_zero_ae
    exact Eventually.of_forall fun s hs => by
      have hsO : s ∈ O := hab ⟨lt_of_lt_of_le (lt_min hax hy.1) (le_of_lt hs.1),
        lt_of_le_of_lt hs.2 (max_lt hxb hy.2)⟩
      simp [hsO]
  have h := flattenValues_sub hO.measurableSet x y
  rw [hzero] at h
  exact sub_eq_zero.mp h

 theorem flattenValues_close {O : Set ℝ} (hO : MeasurableSet O) (hOfin : volume O ≠ ∞) (t : ℝ) :
    |flattenValues O t - t| ≤ (volume O).toReal := by
  have hI : IntervalIntegrable (O.indicator (fun _ => (1 : ℝ))) volume 0 t := by
    apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 t).mono_fun
      ((measurable_const.indicator hO).aestronglyMeasurable)
    exact Eventually.of_forall fun s => by by_cases hs : s ∈ O <;> simp [hs]
  have hsum : flattenValues O t + (∫ s in (0 : ℝ)..t, O.indicator (fun _ => (1 : ℝ)) s) = t := by
    rw [flattenValues, ← intervalIntegral.integral_add (flattenValues_integrable hO 0 t) hI]
    have heq : (fun s => Oᶜ.indicator (fun _ => (1 : ℝ)) s +
        O.indicator (fun _ => (1 : ℝ)) s) = fun _ => (1 : ℝ) := by
      funext s
      by_cases hs : s ∈ O <;> simp [hs]
    rw [heq, intervalIntegral.integral_const]
    simp
  have hbound := intervalIntegral.norm_integral_le_integral_norm_uIoc
    (f := O.indicator (fun _ => (1 : ℝ))) (a := 0) (b := t) (μ := volume)
  have heq : (fun s => ‖O.indicator (fun _ => (1 : ℝ)) s‖) =
      O.indicator (fun _ => (1 : ℝ)) := by
    funext s
    by_cases hs : s ∈ O <;> simp [hs]
  rw [heq] at hbound
  change ‖∫ s in (0 : ℝ)..t, O.indicator (fun _ => (1 : ℝ)) s‖ ≤
    ∫ s, O.indicator (1 : ℝ → ℝ) s ∂(volume.restrict (Ι (0 : ℝ) t)) at hbound
  rw [integral_indicator_one hO] at hbound
  have hm : ((volume.restrict (Ι (0 : ℝ) t)) O).toReal ≤ (volume O).toReal :=
    ENNReal.toReal_mono hOfin (Measure.restrict_apply_le _ _)
  have he : flattenValues O t - t = -(∫ s in (0 : ℝ)..t, O.indicator (fun _ => (1 : ℝ)) s) := by
    linarith
  rw [he, abs_neg]
  have hb : |∫ s in (0 : ℝ)..t, O.indicator (fun _ => (1 : ℝ)) s| ≤
      ((volume.restrict (Ι (0 : ℝ) t)) O).toReal := by
    simpa only [Real.norm_eq_abs, measureReal_def] using hbound
  exact hb.trans hm

end CircleDomainRigidity

end

end OAI
