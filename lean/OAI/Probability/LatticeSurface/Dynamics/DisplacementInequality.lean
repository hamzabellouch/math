import Mathlib
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

def velocity (f : ℝ → ℝ) (a b p : ℝ) : ℝ :=
  (∫ t in a..b, f t) / f (quantile f a b p)

lemma velocity_pos {f : ℝ → ℝ} {a b p : ℝ} (hf : Continuous f)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) (hp : p ∈ Ioo 0 1) :
    0 < velocity f a b p :=
  div_pos (integral_positive hf hpos hab) (hpos _ (quantile_mem_Ioo hf hpos hab hp))

lemma continuousOn_velocity {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) :
    ContinuousOn (velocity f a b) (Ioo 0 1) := by
  intro p hp
  exact (continuousAt_const.div (hf.continuousAt.comp (quantile_continuousAt hf hpos hab hp))
    (hpos _ (quantile_mem_Ioo hf hpos hab hp)).ne').continuousWithinAt

lemma sqrt_reciprocal_product {x y : ℝ} (_hx : 0 < x) (_hy : 0 < y) :
    Real.sqrt (x*y) = 1 / Real.sqrt ((1/x)*(1/y)) := by
  simp only [one_div, ← mul_inv, Real.sqrt_inv, inv_inv]

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
    (hf : Continuous f) (hg : Continuous g)
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

lemma transport_amgm {F G x y z : ℝ} (hF : 0 < F) (hG : 0 < G)
    (hx : 0 < x) (hy : 0 < y) (hz : Real.sqrt (x*y) ≤ z) :
    Real.sqrt (F*G) ≤ z*((F/x+G/y)/2) := by
  have hp := div_pos hF hx
  have hq := div_pos hG hy
  have hsum : 2*Real.sqrt ((F/x)*(G/y)) ≤ F/x+G/y := by
    simpa only [one_mul] using
      (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt ((F/x)*(G/y)))).mp
        (amgm_ratio_ge_one hp hq)
  have hid : Real.sqrt (x*y)*Real.sqrt ((F/x)*(G/y)) = Real.sqrt (F*G) := by
    rw [← Real.sqrt_mul (mul_pos hx hy).le]
    congr 1
    field_simp
  calc
    Real.sqrt (F*G) = Real.sqrt (x*y)*Real.sqrt ((F/x)*(G/y)) := hid.symm
    _ ≤ Real.sqrt (x*y)*((F/x+G/y)/2) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    _ ≤ z*((F/x+G/y)/2) := mul_le_mul_of_nonneg_right hz (by positivity)

lemma midpoint_quantile_integral_lower {f g h : ℝ → ℝ} {a b c d l r : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x) (hgpos : ∀ x ∈ Ioo c d, 0 < g x)
    (hab : a < b) (hcd : c < d) (hl : 0 < l) (hr : r < 1) (hlr : l ≤ r)
    (hmid : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d, Real.sqrt (f x*g y) ≤ h ((x+y)/2)) :
    (r-l)*Real.sqrt ((∫ x in a..b, f x)*(∫ y in c..d, g y)) ≤
    ∫ x in ((quantile f a b l+quantile g c d l)/2)..
      ((quantile f a b r+quantile g c d r)/2), h x := by
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
      (fun p => h ((quantile f a b p+quantile g c d p)/2)*
        ((velocity f a b p+velocity g c d p)/2)) volume l r :=
    ((hh.comp_continuousOn ((hcqf.add hcqg).div_const 2)).mul
      ((hcvf.add hcvg).div_const 2)).intervalIntegrable
  rw [← midpoint_quantile_substitution hf hg hfpos hgpos hab hcd hl hr hlr]
  have hle := intervalIntegral.integral_mono_on hlr
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => Real.sqrt ((∫ x in a..b, f x)*(∫ y in c..d, g y))) volume l r) hi
    (fun p hp => transport_amgm (integral_positive hf hfpos hab)
      (integral_positive hg hgpos hcd)
      (hfpos _ (quantile_mem_Ioo hf hfpos hab (hsub (by simpa [uIcc_of_le hlr] using hp))))
      (hgpos _ (quantile_mem_Ioo hg hgpos hcd (hsub (by simpa [uIcc_of_le hlr] using hp))))
      (hmid _ (quantile_mem_Ioo hf hfpos hab (hsub (by simpa [uIcc_of_le hlr] using hp)))
        _ (quantile_mem_Ioo hg hgpos hcd (hsub (by simpa [uIcc_of_le hlr] using hp)))))
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using hle

theorem interval_prekopa_leindler {f g h : ℝ → ℝ} {a b c d : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x) (hgpos : ∀ x ∈ Ioo c d, 0 < g x)
    (hab : a < b) (hcd : c < d)
    (hnonneg : ∀ z ∈ Icc ((a+c)/2) ((b+d)/2), 0 ≤ h z)
    (hmid : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d, Real.sqrt (f x*g y) ≤ h ((x+y)/2)) :
    Real.sqrt ((∫ x in a..b, f x)*(∫ y in c..d, g y)) ≤
      ∫ z in ((a+c)/2)..((b+d)/2), h z := by
  let S := Real.sqrt ((∫ x in a..b, f x)*(∫ y in c..d, g y))
  have hbound (l r : ℝ) (hl : 0 < l) (hr : r < 1) (hlr : l ≤ r) :
      (r-l)*S ≤ ∫ z in ((a+c)/2)..((b+d)/2), h z := by
    have hl1 : l ∈ Icc (0:ℝ) 1 := ⟨hl.le, (hlr.trans_lt hr).le⟩
    have hr1 : r ∈ Icc (0:ℝ) 1 := ⟨(hl.trans_le hlr).le, hr.le⟩
    have hfl := quantile_mem hf hfpos hab hl1
    have hgl := quantile_mem hg hgpos hcd hl1
    have hfr := quantile_mem hf hfpos hab hr1
    have hgr := quantile_mem hg hgpos hcd hr1
    have hfm := (quantile_strictMonoOn hf hfpos hab).monotoneOn hl1 hr1 hlr
    have hgm := (quantile_strictMonoOn hg hgpos hcd).monotoneOn hl1 hr1 hlr
    exact (midpoint_quantile_integral_lower hf hg hh hfpos hgpos hab hcd hl hr hlr hmid).trans
      (intervalIntegral.integral_mono_interval (by linarith [hfl.1, hgl.1]) (by linarith) (by linarith [hfr.2, hgr.2])
        ((ae_restrict_mem measurableSet_Ioc).mono fun z hz => hnonneg z
          (Ioc_subset_Icc_self hz)) (hh.intervalIntegrable _ _))
  have heps : Tendsto (fun n : ℕ => 1/((n:ℝ)+3)) atTop (𝓝 0) := by
    have hn := (tendsto_add_atTop_iff_nat 2).mpr
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
    convert hn using 1; simp [Nat.cast_add, Nat.cast_ofNat]; ring_nf
  have hlim : Tendsto (fun n : ℕ => (1-1/((n:ℝ)+3)-1/((n:ℝ)+3))*S) atTop (𝓝 S) := by
    convert ((tendsto_const_nhds.sub heps).sub heps).mul_const S using 1; simp
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
