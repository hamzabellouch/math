import Mathlib
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

lemma weighted_transport_amgm {F G x y z s t : ℝ} (hF : 0 < F) (hG : 0 < G)
    (hx : 0 < x) (hy : 0 < y) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1)
    (hz : x^s*y^t ≤ z) : F^s*G^t ≤ z*(s*(F/x)+t*(G/y)) := by
  have hp := div_pos hF hx
  have hq := div_pos hG hy
  have hmean := Real.geom_mean_le_arith_mean2_weighted hs ht hp.le hq.le hst
  have hid : (x^s*y^t)*((F/x)^s*(G/y)^t) = F^s*G^t := by
    rw [Real.div_rpow hF.le hx.le, Real.div_rpow hG.le hy.le]
    field_simp
  calc
    F^s*G^t = (x^s*y^t)*((F/x)^s*(G/y)^t) := hid.symm
    _ ≤ (x^s*y^t)*(s*(F/x)+t*(G/y)) :=
      mul_le_mul_of_nonneg_left hmean (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hy.le _))
    _ ≤ z*(s*(F/x)+t*(G/y)) := mul_le_mul_of_nonneg_right hz (by positivity)

lemma weighted_quantile_substitution {f g h : ℝ → ℝ} {a b c d l r s t : ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x) (hgpos : ∀ x ∈ Ioo c d, 0 < g x)
    (hab : a < b) (hcd : c < d) (hl : 0 < l) (hr : r < 1) (hlr : l ≤ r)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∫ p in l..r, h (s*quantile f a b p+t*quantile g c d p) *
        (s*velocity f a b p+t*velocity g c d p)) =
    ∫ x in (s*quantile f a b l+t*quantile g c d l)..
      (s*quantile f a b r+t*quantile g c d r), h x := by
  have hsub : uIcc l r ⊆ Ioo (0:ℝ) 1 := by
    rw [uIcc_of_le hlr]
    intro p hp
    exact ⟨hl.trans_le hp.1, hp.2.trans_lt hr⟩
  apply intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
  · intro p hp
    exact (((quantile_continuousAt hf hfpos hab (hsub hp)).const_mul s).add
      ((quantile_continuousAt hg hgpos hcd (hsub hp)).const_mul t)).continuousWithinAt
  · intro p hp
    have hp' : p ∈ Ioo (0:ℝ) 1 := hsub (Ioo_subset_Icc_self hp)
    exact ((quantile_hasDerivAt hf hfpos hab hp').const_mul s).add
      ((quantile_hasDerivAt hg hgpos hcd hp').const_mul t)
  · intro p hp
    have hp' : p ∈ Ioo (0:ℝ) 1 := hsub (Ioo_subset_Icc_self hp)
    exact add_nonneg (mul_nonneg hs (velocity_pos hf hfpos hab hp').le)
      (mul_nonneg ht (velocity_pos hg hgpos hcd hp').le)

lemma weighted_quantile_integral_lower {f g h : ℝ → ℝ} {a b c d l r s t : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x) (hgpos : ∀ x ∈ Ioo c d, 0 < g x)
    (hab : a < b) (hcd : c < d) (hl : 0 < l) (hr : r < 1) (hlr : l ≤ r)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1)
    (hmid : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d, (f x)^s*(g y)^t ≤ h (s*x+t*y)) :
    (r-l)*((∫ x in a..b, f x)^s*(∫ y in c..d, g y)^t) ≤
    ∫ x in (s*quantile f a b l+t*quantile g c d l)..
      (s*quantile f a b r+t*quantile g c d r), h x := by
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
  have hi : IntervalIntegrable
      (fun p => h (s*quantile f a b p+t*quantile g c d p)*
        (s*velocity f a b p+t*velocity g c d p)) volume l r :=
    ((hh.comp_continuousOn ((hcqf.const_mul s).add (hcqg.const_mul t))).mul
      ((hcvf.const_mul s).add (hcvg.const_mul t))).intervalIntegrable
  rw [← weighted_quantile_substitution hf hg hfpos hgpos hab hcd hl hr hlr hs ht]
  have hle := intervalIntegral.integral_mono_on hlr
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (∫ x in a..b, f x)^s*(∫ y in c..d, g y)^t) volume l r) hi
    (fun p hp => weighted_transport_amgm (integral_positive hf hfpos hab)
      (integral_positive hg hgpos hcd)
      (hfpos _ (quantile_mem_Ioo hf hfpos hab (hsub (by simpa [uIcc_of_le hlr] using hp))))
      (hgpos _ (quantile_mem_Ioo hg hgpos hcd (hsub (by simpa [uIcc_of_le hlr] using hp)))) hs ht hst
      (hmid _ (quantile_mem_Ioo hf hfpos hab (hsub (by simpa [uIcc_of_le hlr] using hp)))
        _ (quantile_mem_Ioo hg hgpos hcd (hsub (by simpa [uIcc_of_le hlr] using hp)))))
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using hle

theorem interval_weighted_prekopa_leindler {f g h : ℝ → ℝ} {a b c d s t : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x) (hgpos : ∀ x ∈ Ioo c d, 0 < g x)
    (hab : a < b) (hcd : c < d) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1)
    (hnonneg : ∀ z ∈ Icc (s*a+t*c) (s*b+t*d), 0 ≤ h z)
    (hmid : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d, (f x)^s*(g y)^t ≤ h (s*x+t*y)) :
    (∫ x in a..b, f x)^s*(∫ y in c..d, g y)^t ≤
      ∫ z in (s*a+t*c)..(s*b+t*d), h z := by
  let S := (∫ x in a..b, f x)^s*(∫ y in c..d, g y)^t
  have hbound (l r : ℝ) (hl : 0 < l) (hr : r < 1) (hlr : l ≤ r) :
      (r-l)*S ≤ ∫ z in (s*a+t*c)..(s*b+t*d), h z := by
    have hl1 : l ∈ Icc (0:ℝ) 1 := ⟨hl.le, (hlr.trans_lt hr).le⟩
    have hr1 : r ∈ Icc (0:ℝ) 1 := ⟨(hl.trans_le hlr).le, hr.le⟩
    have hfl := quantile_mem hf hfpos hab hl1
    have hgl := quantile_mem hg hgpos hcd hl1
    have hfr := quantile_mem hf hfpos hab hr1
    have hgr := quantile_mem hg hgpos hcd hr1
    have hfm := (quantile_strictMonoOn hf hfpos hab).monotoneOn hl1 hr1 hlr
    have hgm := (quantile_strictMonoOn hg hgpos hcd).monotoneOn hl1 hr1 hlr
    exact (weighted_quantile_integral_lower hf hg hh hfpos hgpos hab hcd hl hr hlr hs ht hst hmid).trans
      (intervalIntegral.integral_mono_interval
        (add_le_add (mul_le_mul_of_nonneg_left hfl.1 hs) (mul_le_mul_of_nonneg_left hgl.1 ht))
        (add_le_add (mul_le_mul_of_nonneg_left hfm hs) (mul_le_mul_of_nonneg_left hgm ht))
        (add_le_add (mul_le_mul_of_nonneg_left hfr.2 hs) (mul_le_mul_of_nonneg_left hgr.2 ht))
        ((ae_restrict_mem measurableSet_Ioc).mono fun z hz => hnonneg z
          (Ioc_subset_Icc_self hz)) (hh.intervalIntegrable _ _))
  have heps : Tendsto (fun n : ℕ => 1/((n:ℝ)+3)) atTop (𝓝 0) := by
    have hn := (tendsto_add_atTop_iff_nat 2).mpr
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
    norm_num [Nat.cast_add, Nat.cast_ofNat, add_assoc] at hn
    simpa only [one_div] using hn
  have hlim : Tendsto (fun n : ℕ => (1-1/((n:ℝ)+3)-1/((n:ℝ)+3))*S) atTop (𝓝 S) := by
    convert ((tendsto_const_nhds.sub heps).sub heps).mul_const S using 1
    simp
  apply le_of_tendsto hlim
  filter_upwards [] with n
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hp : 0 < 1/((n:ℝ)+3) := by positivity
  have hsmall : 1/((n:ℝ)+3) ≤ 1/3 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  exact hbound _ _ hp (by linarith) (by linarith)

end FacetVolume

end

end OAI
