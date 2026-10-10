import Mathlib
import OAI.Probability.LatticeSurface.Convexity.FacetQuantile
import OAI.Probability.LatticeSurface.Convexity.InteriorQuantile
import OAI.Probability.LatticeSurface.Convexity.QuantileCentroid

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace SliceTransport

lemma amgm_ratio_ge_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1 ≤ (x+y)/(2*Real.sqrt (x*y)) := by
  have hs : 0 < Real.sqrt (x*y) := Real.sqrt_pos.2 (mul_pos hx hy)
  have hsq := Real.sq_sqrt (mul_pos hx hy).le
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt (x*y))).2
  nlinarith [sq_nonneg (x-y)]

lemma amgm_ratio_quantitative {x y M : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxM : x ≤ M) (hyM : y ≤ M) :
    1 + (x-y)^2/(8*M^2) ≤ (x+y)/(2*Real.sqrt (x*y)) := by
  have hM : 0 < M := hx.trans_le hxM
  have hs : 0 < Real.sqrt (x*y) := Real.sqrt_pos.2 (mul_pos hx hy)
  have hsq := Real.sq_sqrt (mul_pos hx hy).le
  have hsM : Real.sqrt (x*y) ≤ M := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact hM.le
    · nlinarith [mul_le_mul hxM hyM hy.le hM.le]
  have hsum : 2*Real.sqrt (x*y) ≤ x+y := by
    have h := amgm_ratio_ge_one hx hy
    simpa only [one_mul] using (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt (x*y))).mp h
  have hprod : 2*Real.sqrt (x*y)*(x+y+2*Real.sqrt (x*y)) ≤ 8*M^2 := by
    have h := mul_le_mul (by linarith : 2*Real.sqrt (x*y) ≤ 2*M)
      (by linarith : x+y+2*Real.sqrt (x*y) ≤ 4*M) (by positivity) (by positivity : 0 ≤ 2*M)
    nlinarith
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt (x*y))).2
  have heq : (x-y)^2 = (x+y-2*Real.sqrt (x*y))*(x+y+2*Real.sqrt (x*y)) := by
    nlinarith
  have h := mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr hsum)
  have hbound : 2*Real.sqrt (x*y)*(x-y)^2 ≤ (x+y-2*Real.sqrt (x*y))*(8*M^2) := by
    rw [heq]
    nlinarith [h]
  have hden : 0 < 8*M^2 := by positivity
  have hh : (x-y)^2/(8*M^2)*(2*Real.sqrt (x*y)) ≤ x+y-2*Real.sqrt (x*y) := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hden).2 (by nlinarith [hbound])
  nlinarith

lemma midpoint_quantile_substitution {f g h : ℝ → ℝ} {a b c d l r : ℝ}
    (hf : IntervalDensity f a b) (hg : IntervalDensity g c d)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x) (hgpos : ∀ x ∈ Ioo c d, 0 < g x)
    (hab : a < b) (hcd : c < d) (hl : 0 < l) (hr : r < 1) (hlr : l ≤ r) :
    (∫ p in l..r, h ((quantile f a b p + quantile g c d p)/2) *
        ((velocity f a b p + velocity g c d p)/2)) =
    ∫ x in ((quantile f a b l+quantile g c d l)/2)..
      ((quantile f a b r+quantile g c d r)/2), h x := by
  have hsub : uIcc l r ⊆ Ioo (0:ℝ) 1 := by
    rw [uIcc_of_le hlr]
    intro p hp
    exact ⟨hl.trans_le hp.1, hp.2.trans_lt hr⟩
  apply intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
  · intro p hp
    exact (((quantile_continuousAt hf hfpos hab (hsub hp)).add
      (quantile_continuousAt hg hgpos hcd (hsub hp))).div_const 2).continuousWithinAt
  · intro p hp
    have hp' : p ∈ Ioo (0:ℝ) 1 := hsub (Ioo_subset_Icc_self hp)
    exact ((quantile_hasDerivAt hf hfpos hab hp').add
      (quantile_hasDerivAt hg hgpos hcd hp')).div_const 2
  · intro p hp
    have hp' : p ∈ Ioo (0:ℝ) 1 := hsub (Ioo_subset_Icc_self hp)
    exact (div_pos (add_pos (velocity_pos hf hfpos hab hp')
      (velocity_pos hg hgpos hcd hp')) (by norm_num)).le

lemma transport_amgm_quantitative {F G x y z C p : ℝ}
    (hF : 0 < F) (hG : 0 < G) (hx : 0 < x) (hy : 0 < y)
    (hC : 0 < C) (hp : 0 < p) (hv : F/x ≤ C/p) (hw : G/y ≤ C/p)
    (hz : Real.sqrt (x*y) ≤ z) :
    Real.sqrt (F*G)*(1+(p*(F/x-G/y))^2/(8*C^2)) ≤ z*((F/x+G/y)/2) := by
  have hpv := div_pos hF hx
  have hpw := div_pos hG hy
  have hs : 0 < Real.sqrt ((F/x)*(G/y)) := Real.sqrt_pos.2 (mul_pos hpv hpw)
  have ha : 1+(p*(F/x-G/y))^2/(8*C^2) ≤
      (F/x+G/y)/(2*Real.sqrt ((F/x)*(G/y))) := by
    convert amgm_ratio_quantitative hpv hpw hv hw using 1
    field_simp
  have hid : Real.sqrt (x*y)*Real.sqrt ((F/x)*(G/y)) = Real.sqrt (F*G) := by
    rw [← Real.sqrt_mul (mul_pos hx hy).le]
    congr 1
    field_simp
  calc
    _ ≤ Real.sqrt (F*G)*((F/x+G/y)/(2*Real.sqrt ((F/x)*(G/y)))) :=
      mul_le_mul_of_nonneg_left ha (Real.sqrt_nonneg _)
    _ = Real.sqrt (x*y)*((F/x+G/y)/2) := by
      rw [← hid]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hz (by positivity)

lemma integral_sq_ge_sq_integral {E : ℝ → ℝ}
    (hi : IntervalIntegrable E volume 0 1)
    (hi2 : IntervalIntegrable (fun p => E p ^ 2) volume 0 1) :
    (∫ p in (0:ℝ)..1, E p)^2 ≤ ∫ p in (0:ℝ)..1, E p ^2 := by
  let m := ∫ p in (0:ℝ)..1, E p
  have h := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ) ≤ 1)
    (hi.const_mul (2*m)) (hi2.add intervalIntegrable_const)
    (fun p _ => show 2*m*E p ≤ E p^2+m^2 by nlinarith [sq_nonneg (E p-m)])
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi2 intervalIntegrable_const,
    intervalIntegral.integral_const] at h
  change 2*m*m ≤ (∫ p in (0:ℝ)..1, E p^2) + (1-0)*m^2 at h
  change m^2 ≤ _
  nlinarith [h]

lemma integral_difference_velocity_sq {f g : ℝ → ℝ} {a b c d C : ℝ}
    (hf : IntervalDensity f a b) (hg : IntervalDensity g c d)
    (hab : a < b) (hcd : c < d)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x) (hgpos : ∀ y ∈ Ioo c d, 0 < g y)
    (hvf : ∀ p ∈ Ioo 0 1, velocity f a b p ≤ C/p)
    (hvg : ∀ p ∈ Ioo 0 1, velocity g c d p ≤ C/p) :
    IntervalIntegrable (fun p => (p*(velocity f a b p-velocity g c d p))^2) volume 0 1 := by
  apply intervalIntegrable_of_interior_bound (C := C^2) (by norm_num)
    ((continuousOn_id.mul ((continuousOn_velocity hf hfpos hab).sub
      (continuousOn_velocity hg hgpos hcd))).pow 2)
  intro p hp
  have hv := probability_velocity_bound hf hab hfpos hvf hp
  have hw := probability_velocity_bound hg hcd hgpos hvg hp
  change |(p*(velocity f a b p-velocity g c d p))^2| ≤ C^2
  rw [abs_of_nonneg (sq_nonneg _)]
  have hh : |p*(velocity f a b p-velocity g c d p)| ≤ C := by
    rw [abs_le]
    constructor <;> nlinarith [hv.1,hv.2,hw.1,hw.2]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (hv.1.trans hv.2)).mpr hh

lemma quantitative_integrand_integrable {f g : ℝ → ℝ} {a b c d C : ℝ}
    (hf : IntervalDensity f a b) (hg : IntervalDensity g c d)
    (hab : a < b) (hcd : c < d)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x) (hgpos : ∀ y ∈ Ioo c d, 0 < g y)
    (hvf : ∀ p ∈ Ioo 0 1, velocity f a b p ≤ C/p)
    (hvg : ∀ p ∈ Ioo 0 1, velocity g c d p ≤ C/p) :
    IntervalIntegrable (fun p => 1+(p*(velocity f a b p-velocity g c d p))^2/(8*C^2)) volume 0 1 :=
  intervalIntegrable_const.add ((integral_difference_velocity_sq hf hg hab hcd hfpos hgpos hvf hvg).div_const _)

lemma midpoint_quantile_defect_lower {f g h : ℝ → ℝ} {a b c d C l r : ℝ}
    (hf : IntervalDensity f a b) (hg : IntervalDensity g c d)
    (hh : IntervalDensity h ((a+c)/2) ((b+d)/2))
    (hab : a < b) (hcd : c < d) (hC : 0 < C)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x) (hgpos : ∀ y ∈ Ioo c d, 0 < g y)
    (hvf : ∀ p ∈ Ioo 0 1, velocity f a b p ≤ C/p)
    (hvg : ∀ p ∈ Ioo 0 1, velocity g c d p ≤ C/p)
    (hmid : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d, Real.sqrt (f x*g y) ≤ h ((x+y)/2))
    (hl : 0 < l) (hr : r < 1) (hlr : l ≤ r) :
    Real.sqrt ((∫ x in a..b, f x)*(∫ y in c..d, g y)) *
      (∫ p in l..r, 1+(p*(velocity f a b p-velocity g c d p))^2/(8*C^2)) ≤
    ∫ z in ((quantile f a b l+quantile g c d l)/2)..
      ((quantile f a b r+quantile g c d r)/2), h z := by
  have hsub : uIcc l r ⊆ Ioo (0:ℝ) 1 := by
    rw [uIcc_of_le hlr]
    intro p hp
    exact ⟨hl.trans_le hp.1, hp.2.trans_lt hr⟩
  have hcqf : ContinuousOn (quantile f a b) (uIcc l r) := fun p hp =>
    (quantile_continuousAt hf hfpos hab (hsub hp)).continuousWithinAt
  have hcqg : ContinuousOn (quantile g c d) (uIcc l r) := fun p hp =>
    (quantile_continuousAt hg hgpos hcd (hsub hp)).continuousWithinAt
  have hcvf := (continuousOn_velocity hf hfpos hab).mono hsub
  have hcvg := (continuousOn_velocity hg hgpos hcd).mono hsub
  have hmap : MapsTo (fun p => (quantile f a b p+quantile g c d p)/2)
      (uIcc l r) (Ioo ((a+c)/2) ((b+d)/2)) := by
    intro p hp
    have hqf := quantile_mem_Ioo hf hfpos hab (hsub hp)
    have hqg := quantile_mem_Ioo hg hgpos hcd (hsub hp)
    constructor <;> linarith [hqf.1,hqf.2,hqg.1,hqg.2]
  have hi : IntervalIntegrable
      (fun p => h ((quantile f a b p+quantile g c d p)/2)*
        ((velocity f a b p+velocity g c d p)/2)) volume l r :=
    ((hh.continuous.comp ((hcqf.add hcqg).div_const 2) hmap).mul
      ((hcvf.add hcvg).div_const 2)).intervalIntegrable
  have hiφ : IntervalIntegrable
      (fun p => 1+(p*(velocity f a b p-velocity g c d p))^2/(8*C^2)) volume l r := by
    apply (quantitative_integrand_integrable hf hg hab hcd hfpos hgpos hvf hvg).mono_set
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hsub.trans Ioo_subset_Icc_self
  rw [← midpoint_quantile_substitution hf hg hfpos hgpos hab hcd hl hr hlr,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hlr (hiφ.const_mul _) hi
  intro p hp
  have hp' : p ∈ Ioo (0:ℝ) 1 := hsub (by simpa only [uIcc_of_le hlr] using hp)
  exact transport_amgm_quantitative (integral_positive hf hfpos hab)
    (integral_positive hg hgpos hcd)
    (hfpos _ (quantile_mem_Ioo hf hfpos hab hp'))
    (hgpos _ (quantile_mem_Ioo hg hgpos hcd hp')) hC hp'.1 (hvf p hp') (hvg p hp')
    (hmid _ (quantile_mem_Ioo hf hfpos hab hp') _ (quantile_mem_Ioo hg hgpos hcd hp'))

end SliceTransport

end

end OAI
