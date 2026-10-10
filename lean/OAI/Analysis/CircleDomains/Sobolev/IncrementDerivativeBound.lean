import OAI.Analysis.CircleDomains.Sobolev.IntegralLineAbsoluteContinuity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

namespace OAI

/-! Increment domination passes to derivatives. The integral criterion
then yields the linewise weak-gradient bound used by the barrier. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem abs_derivative_le_of_increment_domination
    {f F : ℝ → ℝ} {x f' F' : ℝ}
    (hf : HasDerivAt f f' x) (hF : HasDerivAt F F' x)
    (h : ∀ᶠ y in 𝓝 x, |f y - f x| ≤ |F y - F x|) : |f'| ≤ |F'| := by
  apply le_of_tendsto_of_tendsto hf.tendsto_slope.abs hF.tendsto_slope.abs
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with y hy
  simp only [slope, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)

theorem ae_abs_deriv_le_of_integral_bound
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b)
    (hgnonneg : ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ g x)
    (hbound : ∀x ∈ Icc a b, ∀y ∈ Icc a b,
      |f x - f y| ≤ ∫t in uIoc x y, g t) :
    ∀ᵐ x ∂volume.restrict (Icc a b), |deriv f x| ≤ g x := by
  have hac : AbsolutelyContinuousOnInterval f a b :=
    absolutelyContinuousOnInterval_of_integral_bound hg (by
      simpa only [uIcc_of_le hab, Real.dist_eq] using hbound)
  have hd := hac.ae_differentiableAt
  have hH := hg.ae_hasDerivAt_integral
  have hi : ∀ᵐ x ∂volume.restrict (Icc a b), x ∈ Ioo a b := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff], show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff]] with x hxa hxb hx
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_of_ae hH, hgnonneg, hi] with x hdx hHx hpos hx
  have hdx' : DifferentiableAt ℝ f x := hdx (by simpa only [uIcc_of_le hab] using ⟨hx.1.le, hx.2.le⟩)
  have hHx' := hHx (by simpa only [uIcc_of_le hab] using (show x ∈ Icc a b from ⟨hx.1.le, hx.2.le⟩))
    a left_mem_uIcc
  have hdom : ∀ᶠ y in 𝓝 x, |f y - f x| ≤
      |(∫t in a..y, g t) - ∫t in a..x, g t| := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    apply (hbound y ⟨hy.1.le, hy.2.le⟩ x ⟨hx.1.le, hx.2.le⟩).trans
    rw [intervalIntegral.integral_interval_sub_left
      (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc
        (uIcc_subset_uIcc left_mem_uIcc (by simpa only [uIcc_of_le hab] using (show y ∈ Icc a b from ⟨hy.1.le, hy.2.le⟩)))))
      (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc
        (uIcc_subset_uIcc left_mem_uIcc (by simpa only [uIcc_of_le hab] using (show x ∈ Icc a b from ⟨hx.1.le, hx.2.le⟩))))),
      intervalIntegral.abs_intervalIntegral_eq]
    simpa only [uIoc_comm x y] using (le_abs_self (∫t in uIoc y x, g t))
  simpa only [abs_of_nonneg hpos] using
    abs_derivative_le_of_increment_domination hdx'.hasDerivAt hHx' hdom

end CircleDomainRigidity

end OAI
