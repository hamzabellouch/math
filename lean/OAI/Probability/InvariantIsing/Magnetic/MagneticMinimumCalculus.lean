import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import OAI.Probability.InvariantIsing.Magnetic.MagneticImplicitBias

namespace OAI

/-! Necessary derivative signs at minima, for the inverse-coordinate
parabolic comparison on the closed mean-spin interval. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma second_derivative_nonneg_at_local_min {f f' : ℝ → ℝ} {a c : ℝ}
    (hm : IsLocalMin f a)
    (hf : ∀ᶠ x in 𝓝 a, HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' c a) : 0 ≤ c := by
  have hfa := hf.self_of_nhds
  have hz : f' a = 0 := hm.hasDerivAt_eq_zero hfa
  have hd := (hasDerivAt_iff_tendsto_slope_left_right.mp hf').2
  have hd' : Tendsto (fun x : ℝ => f' x / (2 * (x - a)))
      (𝓝[>] a) (𝓝 (c / 2)) := by
    have hh := hd.div_const 2
    convert hh using 1
    funext x
    rw [slope_def_field, hz, sub_zero, mul_comm (2 : ℝ) (x - a), div_mul_eq_div_div]
  have hnum : ∀ᶠ x in 𝓝[>] a, HasDerivAt (fun y => f y - f a) (f' x) x := by
    filter_upwards [hf.filter_mono nhdsWithin_le_nhds] with x hx
    exact hx.sub_const (f a)
  have hden : ∀ᶠ x in 𝓝[>] a,
      HasDerivAt (fun y : ℝ => (y - a) ^ 2) (2 * (x - a)) x := by
    filter_upwards [] with x
    convert ((hasDerivAt_id x).sub_const a).pow 2 using 1
    · funext y
      rfl
    · simp
  have hne : ∀ᶠ x in 𝓝[>] a, 2 * (x - a) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hx.ne')
  have hn0 : Tendsto (fun x => f x - f a) (𝓝[>] a) (𝓝 0) := by
    simpa only [sub_self] using (hfa.continuousAt.sub_const (f a)).mono_left
      nhdsWithin_le_nhds
  have hd0 : Tendsto (fun x : ℝ => (x - a) ^ 2) (𝓝[>] a) (𝓝 0) := by
    have hh : ContinuousAt (fun x : ℝ => (x - a) ^ 2) a := by fun_prop
    simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0)] using
      hh.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := HasDerivAt.lhopital_zero_nhdsGT hnum hden hne hn0 hd0 hd'
  have hnon : ∀ᶠ x in 𝓝[>] a, 0 ≤ (f x - f a) / (x - a) ^ 2 := by
    filter_upwards [hm.filter_mono nhdsWithin_le_nhds] with x hx
    exact div_nonneg (sub_nonneg.mpr hx) (sq_nonneg _)
  have : 0 ≤ c / 2 := ge_of_tendsto hlim hnon
  linarith

lemma derivative_nonpos_at_left_min {f : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivAt f d a) (hm : ∀ᶠ x in 𝓝[<] a, f a ≤ f x) : d ≤ 0 := by
  have hl := (hasDerivAt_iff_tendsto_slope_left_right.mp hf).1
  apply le_of_tendsto hl
  filter_upwards [hm, self_mem_nhdsWithin] with x hx hxa
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx) (sub_nonpos.mpr hxa.le)

lemma derivativeWithin_nonpos_at_left_min {f : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivWithinAt f d (Iic a) a)
    (hm : ∀ᶠ x in 𝓝[<] a, f a ≤ f x) : d ≤ 0 := by
  have hl : Tendsto (slope f a) (𝓝[<] a) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : a ∉ Iio a)).mp
      (hf.mono Iio_subset_Iic_self)
  apply le_of_tendsto hl
  filter_upwards [hm, self_mem_nhdsWithin] with x hx hxa
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx) (sub_nonpos.mpr hxa.le)

end InvariantIsing

end

end OAI
