import Mathlib
import OAI.Probability.LatticeSurface.Convexity.FacetQuantile
import OAI.Probability.LatticeSurface.Convexity.InteriorQuantile
import OAI.Probability.LatticeSurface.Convexity.QuantileCentroid
import OAI.Probability.LatticeSurface.Convexity.QuantitativeTransport

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace SliceTransport

lemma integral_bound_of_inner_intervals {φ : ℝ → ℝ} {S H : ℝ}
    (hi : IntervalIntegrable φ volume 0 1)
    (hbound : ∀ l r : ℝ, 0 < l → r < 1 → l ≤ r → S*(∫ p in l..r, φ p) ≤ H) :
    S*(∫ p in (0:ℝ)..1, φ p) ≤ H := by
  let ε (n : ℕ) : ℝ := 1/((n:ℝ)+3)
  have heps : Tendsto ε atTop (𝓝 0) := by
    have hn := (tendsto_add_atTop_iff_nat 2).mpr
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
    convert hn using 1
    simp [ε, Nat.cast_add, Nat.cast_ofNat]
    ring_nf
  have hsmall (n : ℕ) : 0 < ε n ∧ ε n ≤ 1/3 := by
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    constructor
    · exact one_div_pos.mpr (by linarith)
    · exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hecc (n : ℕ) : ε n ∈ Icc (0:ℝ) 1 := by
    have h := hsmall n
    constructor <;> linarith
  have hrecc (n : ℕ) : 1-ε n ∈ Icc (0:ℝ) 1 := by
    have h := hsmall n
    constructor <;> linarith
  have hprim : ContinuousOn (fun r => ∫ p in (0:ℝ)..r, φ p) (Icc 0 1) := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using
      (intervalIntegral.continuousOn_primitive_interval' hi (a := 0) left_mem_uIcc)
  have hil (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : IntervalIntegrable φ volume 0 x := by
    apply hi.mono_set
    rw [uIcc_of_le hx.1, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc_right hx.2
  have hleft : Tendsto (fun n => ∫ p in (0:ℝ)..ε n, φ p) atTop (𝓝 0) := by
    have h := (hprim 0 (by norm_num)).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ε heps
        (Filter.Eventually.of_forall hecc))
    simpa only [intervalIntegral.integral_same, Function.comp_def] using h
  have hright : Tendsto (fun n => ∫ p in (0:ℝ)..1-ε n, φ p) atTop
      (𝓝 (∫ p in (0:ℝ)..1, φ p)) := by
    apply (hprim 1 (by norm_num)).tendsto.comp
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa only [sub_zero] using tendsto_const_nhds.sub heps)
    exact Filter.Eventually.of_forall hrecc
  have hlim : Tendsto (fun n => S*(∫ p in ε n..1-ε n, φ p)) atTop
      (𝓝 (S*(∫ p in (0:ℝ)..1, φ p))) := by
    have heq (n : ℕ) : (∫ p in ε n..1-ε n, φ p) =
        (∫ p in (0:ℝ)..1-ε n, φ p) - ∫ p in (0:ℝ)..ε n, φ p :=
      (intervalIntegral.integral_interval_sub_left (hil _ (hrecc n)) (hil _ (hecc n))).symm
    simp only [heq]
    simpa only [sub_zero] using (hright.sub hleft).const_mul S
  apply le_of_tendsto hlim
  filter_upwards [] with n
  have hs := hsmall n
  exact hbound _ _ hs.1 (by linarith) (by linarith)

lemma integral_displacement_defect {f g h : ℝ → ℝ} {a b c d C : ℝ}
    (hf : IntervalDensity f a b) (hg : IntervalDensity g c d)
    (hh : IntervalDensity h ((a+c)/2) ((b+d)/2))
    (hab : a < b) (hcd : c < d) (hC : 0 < C)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x) (hgpos : ∀ y ∈ Ioo c d, 0 < g y)
    (hvf : ∀ p ∈ Ioo 0 1, velocity f a b p ≤ C/p)
    (hvg : ∀ p ∈ Ioo 0 1, velocity g c d p ≤ C/p)
    (hnonneg : ∀ z, 0 ≤ h z)
    (hmid : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d, Real.sqrt (f x*g y) ≤ h ((x+y)/2)) :
    Real.sqrt ((∫ x in a..b, f x)*(∫ y in c..d, g y)) *
      (1+(∫ p in (0:ℝ)..1, (p*(velocity f a b p-velocity g c d p))^2)/(8*C^2)) ≤
    ∫ z in ((a+c)/2)..((b+d)/2), h z := by
  have hi2 := integral_difference_velocity_sq hf hg hab hcd hfpos hgpos hvf hvg
  have hiφ := quantitative_integrand_integrable hf hg hab hcd hfpos hgpos hvf hvg
  have hint : (∫ p in (0:ℝ)..1, 1+(p*(velocity f a b p-velocity g c d p))^2/(8*C^2)) =
      1+(∫ p in (0:ℝ)..1, (p*(velocity f a b p-velocity g c d p))^2)/(8*C^2) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hi2.div_const _),
      intervalIntegral.integral_div, intervalIntegral.integral_const]
    norm_num
  rw [← hint]
  apply integral_bound_of_inner_intervals hiφ
  intro l r hl hr hlr
  have hl1 : l ∈ Icc (0:ℝ) 1 := ⟨hl.le, (hlr.trans_lt hr).le⟩
  have hr1 : r ∈ Icc (0:ℝ) 1 := ⟨(hl.trans_le hlr).le, hr.le⟩
  have hfl := quantile_mem hf hfpos hab hl1
  have hgl := quantile_mem hg hgpos hcd hl1
  have hfr := quantile_mem hf hfpos hab hr1
  have hgr := quantile_mem hg hgpos hcd hr1
  have hfm := (quantile_strictMonoOn hf hfpos hab).monotoneOn hl1 hr1 hlr
  have hgm := (quantile_strictMonoOn hg hgpos hcd).monotoneOn hl1 hr1 hlr
  exact (midpoint_quantile_defect_lower hf hg hh hab hcd hC hfpos hgpos hvf hvg hmid hl hr hlr).trans
    (intervalIntegral.integral_mono_interval (by linarith [hfl.1,hgl.1]) (by linarith)
      (by linarith [hfr.2,hgr.2]) (Filter.Eventually.of_forall hnonneg) hh.integrable)

lemma centroid_gap_mem {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalDensity f a b) (hab : a < b) (hpos : ∀ x ∈ Ioo a b, 0 < f x) :
    b-(∫ x in a..b, x*f x)/(∫ x in a..b, f x) ∈ Icc 0 (b-a) := by
  rw [← integral_quantile_eq_firstMoment hf hab hpos]
  have hi : IntervalIntegrable (quantile f a b) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using quantile_continuousOn hf hpos hab
  have hl := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    intervalIntegrable_const hi (fun p hp => (quantile_mem hf hpos hab hp).1)
  have hr := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    hi intervalIntegrable_const (fun p hp => (quantile_mem hf hpos hab hp).2)
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hl hr
  constructor <;> linarith

lemma logarithmic_defect_of_quadratic {H S C A D : ℝ}
    (hS : 0 < S) (hC : 0 < C) (hD : D^2 ≤ A^2)
    (hH : S*(1+D^2/(8*C^2)) ≤ H) :
    D^2/(8*C^2+A^2) ≤ Real.log (H/S) := by
  have hden : 0 < 8*C^2 := by positivity
  have hplus : 0 < 1+D^2/(8*C^2) := by positivity
  have hratio : 1+D^2/(8*C^2) ≤ H/S := (le_div_iff₀ hS).mpr (by nlinarith [hH])
  have hlog := Real.one_sub_inv_le_log_of_pos hplus
  have heq : 1-(1+D^2/(8*C^2))⁻¹ = D^2/(8*C^2+D^2) := by
    field_simp
    ring
  rw [heq] at hlog
  exact (div_le_div_of_nonneg_left (sq_nonneg D) (by positivity : 0 < 8*C^2+D^2)
    (by linarith : 8*C^2+D^2 ≤ 8*C^2+A^2)).trans
      (hlog.trans (Real.log_le_log hplus hratio))

theorem interval_facet_deficit {f g h : ℝ → ℝ} {a b c d C A : ℝ}
    (hf : IntervalDensity f a b) (hg : IntervalDensity g c d)
    (hh : IntervalDensity h ((a+c)/2) ((b+d)/2))
    (hab : a < b) (hcd : c < d) (hC : 0 < C)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x) (hgpos : ∀ y ∈ Ioo c d, 0 < g y)
    (hvf : ∀ p ∈ Ioo 0 1, velocity f a b p ≤ C/p)
    (hvg : ∀ p ∈ Ioo 0 1, velocity g c d p ≤ C/p)
    (hwidthf : b-a ≤ A) (hwidthg : d-c ≤ A)
    (hnonneg : ∀ z, 0 ≤ h z)
    (hmid : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d, Real.sqrt (f x*g y) ≤ h ((x+y)/2)) :
    ((b-(∫ x in a..b, x*f x)/(∫ x in a..b, f x))-
      (d-(∫ y in c..d, y*g y)/(∫ y in c..d, g y)))^2/(8*C^2+A^2) ≤
    Real.log ((∫ z in ((a+c)/2)..((b+d)/2), h z)/
      Real.sqrt ((∫ x in a..b, f x)*(∫ y in c..d, g y))) := by
  let E := fun p => p*(velocity f a b p-velocity g c d p)
  have hif := integrable_probability_velocity hf hab hfpos hvf
  have hig := integrable_probability_velocity hg hcd hgpos hvg
  have hi : IntervalIntegrable E volume 0 1 := by
    simpa only [E, mul_sub] using hif.sub hig
  have hi2 := integral_difference_velocity_sq hf hg hab hcd hfpos hgpos hvf hvg
  have hid : (∫ p in (0:ℝ)..1, E p) =
      (b-(∫ x in a..b, x*f x)/(∫ x in a..b, f x))-
        (d-(∫ y in c..d, y*g y)/(∫ y in c..d, g y)) := by
    simp only [E, mul_sub]
    rw [intervalIntegral.integral_sub hif hig, integral_probability_velocity hf hab hfpos hvf,
      integral_probability_velocity hg hcd hgpos hvg]
  have hD := integral_sq_ge_sq_integral hi hi2
  rw [hid] at hD
  have hfmean := centroid_gap_mem hf hab hfpos
  have hgmean := centroid_gap_mem hg hcd hgpos
  have hA : 0 < A := (sub_pos.mpr hab).trans_le hwidthf
  have hdabs : |(b-(∫ x in a..b, x*f x)/(∫ x in a..b, f x))-
      (d-(∫ y in c..d, y*g y)/(∫ y in c..d, g y))| ≤ A := by
    rw [abs_le]
    constructor <;> linarith [hfmean.1,hfmean.2,hgmean.1,hgmean.2]
  apply logarithmic_defect_of_quadratic
    (Real.sqrt_pos.2 (mul_pos (integral_positive hf hfpos hab) (integral_positive hg hgpos hcd))) hC
  · simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hA.le).mpr hdabs
  · refine le_trans ?_ (integral_displacement_defect hf hg hh hab hcd hC hfpos hgpos hvf hvg hnonneg hmid)
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    have hhdiv := div_le_div_of_nonneg_right hD (by positivity : 0 ≤ 8*C^2)
    dsimp only [E] at hhdiv
    linarith

end SliceTransport

end

end OAI
