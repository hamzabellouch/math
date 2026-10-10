import Mathlib
import OAI.Probability.LatticeSurface.Convexity.InteriorQuantile

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace SliceTransport

def velocity (f : ℝ → ℝ) (a b p : ℝ) : ℝ :=
  (∫ t in a..b, f t) / f (quantile f a b p)

lemma velocity_pos {f : ℝ → ℝ} {a b p : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) (hp : p ∈ Ioo 0 1) :
    0 < velocity f a b p :=
  div_pos (integral_positive hf hpos hab) (hpos _ (quantile_mem_Ioo hf hpos hab hp))

lemma continuousOn_velocity {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) :
    ContinuousOn (velocity f a b) (Ioo 0 1) := by
  intro p hp
  exact (continuousAt_const.div ((hf.continuousAt (quantile_mem_Ioo hf hpos hab hp)).comp
    (quantile_continuousAt hf hpos hab hp)) (hpos _ (quantile_mem_Ioo hf hpos hab hp)).ne').continuousWithinAt

lemma IntervalDensity.intervalIntegrable_left {f : ℝ → ℝ} {a b x : ℝ}
    (hf : IntervalDensity f a b) (hx : x ∈ Icc a b) : IntervalIntegrable f volume a x := by
  apply hf.integrable.mono_set
  rw [uIcc_of_le hx.1, uIcc_of_le (hx.1.trans hx.2)]
  exact Icc_subset_Icc_right hx.2

lemma density_le_left_of_le_top {f : ℝ → ℝ} {a b x z : ℝ}
    (hlog : ConcaveOn ℝ (Ioc a b) (Real.log ∘ f))
    (hpos : ∀ u ∈ Ioc a b, 0 < f u) (hx : x ∈ Ioc a b) (hz : z ∈ Ioo a b)
    (hxz : x ≤ z) (htop : f z ≤ f b) : f x ≤ f z := by
  have hl := hlog.left_le_of_le_right'' hx ⟨hz.1.trans hz.2, le_rfl⟩ hxz hz.2
    (Real.log_le_log (hpos z ⟨hz.1,hz.2.le⟩) htop)
  exact (Real.log_le_log_iff (hpos x hx) (hpos z ⟨hz.1,hz.2.le⟩)).mp hl

lemma velocity_le_div_probability {f : ℝ → ℝ} {a b C p : ℝ}
    (hf : IntervalDensity f a b) (hab : a < b)
    (hpos : ∀ x ∈ Ioc a b, 0 < f x)
    (hlog : ConcaveOn ℝ (Ioc a b) (Real.log ∘ f))
    (hwidth : b-a ≤ C) (htop : (∫ t in a..b, f t) ≤ C*f b)
    (hp : p ∈ Ioo 0 1) : velocity f a b p ≤ C/p := by
  have hfpos : ∀ x ∈ Ioo a b, 0 < f x := fun x hx => hpos x (Ioo_subset_Ioc_self hx)
  have hq := quantile_mem_Ioo hf hfpos hab hp
  have hpq := hfpos _ hq
  have hmass := integral_positive hf hfpos hab
  have hC : 0 < C := (sub_pos.mpr hab).trans_le hwidth
  by_cases hsmall : f (quantile f a b p) ≤ f b
  · have hbound : (∫ x in a..quantile f a b p, f x) ≤
        (quantile f a b p-a)*f (quantile f a b p) := by
      have hi := intervalIntegral.integral_mono_on_of_le_Ioo hq.1.le
        (hf.intervalIntegrable_left (Ioo_subset_Icc_self hq)) intervalIntegrable_const
        (fun x hx => density_le_left_of_le_top hlog hpos
          ⟨hx.1, hx.2.le.trans hq.2.le⟩ hq hx.2.le hsmall)
      simpa only [intervalIntegral.integral_const, smul_eq_mul] using hi
    have hcum := cumulative_quantile hf hfpos hab (Ioo_subset_Icc_self hp)
    have hpmass : (∫ x in a..quantile f a b p, f x) = p*(∫ x in a..b, f x) :=
      (div_eq_iff hmass.ne').mp hcum
    have hprob : p*(∫ x in a..b, f x) ≤ C*f (quantile f a b p) := by
      rw [hpmass] at hbound
      have hb : quantile f a b p-a ≤ C := by linarith [hq.2]
      exact hbound.trans (mul_le_mul_of_nonneg_right hb hpq.le)
    rw [velocity, div_le_div_iff₀ hpq hp.1]
    nlinarith [hprob]
  · have hb : f b ≤ f (quantile f a b p) := (not_le.mp hsmall).le
    have hvel : velocity f a b p ≤ C := by
      rw [velocity, div_le_iff₀ hpq]
      exact htop.trans (mul_le_mul_of_nonneg_left hb hC.le)
    exact hvel.trans ((le_div_iff₀ hp.1).mpr (mul_le_of_le_one_right hC.le hp.2.le))

end SliceTransport

end

end OAI
