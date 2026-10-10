import Mathlib
import OAI.Geometry.CAT0Fillings.Transport.RadialCDF

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.RadialSobolev

section
variable {n : ℕ} {ω p R D : ℝ} {f g : ℝ → ℝ}
  (hR : 0 < R) (hD : 0 < D) (hn : 0 < n) (hω : 0 < ω)
  (hf : Continuous f) (hg : Continuous g) (hp : 0 < p)
  (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r)
  (hmass : radialCDF n ω f p R = radialCDF n ω g p D)

lemma radialTransport_zero : radialTransport (f := f) hD.le hn hω hg hp hgp 0 = 0 := by
  change cumulativeInverse _ _ _ (radialCDF n ω f p 0) = 0
  simpa only [radialCDF_zero] using
    cumulativeInverse_left hD.le (radialCDF_continuous hg hp).continuousOn
      (radialCDF_strictMonoOn hn hω hg hp hgp) ⟨le_rfl,hD.le⟩

include hmass in
lemma radialTransport_top : radialTransport (f := f) hD.le hn hω hg hp hgp R = D := by
  change cumulativeInverse _ _ _ (radialCDF n ω f p R) = D
  rw [hmass]
  exact cumulativeInverse_left _ _ _ ⟨hD.le,le_rfl⟩

include hf hfp hmass

lemma radialTransport_strictMonoOn :
    StrictMonoOn (radialTransport (f := f) hD.le hn hω hg hp hgp) (Icc 0 R) := by
  intro x hx y hy hxy
  have hx' := radialTransport_mem (f := f) hD.le hn hω hg hp hgp x
  have hy' := radialTransport_mem (f := f) hD.le hn hω hg hp hgp y
  apply (radialCDF_strictMonoOn hn hω hg hp hgp).lt_iff_lt hx' hy' |>.mp
  rw [radialTransport_cdf hD.le hn hω hf hg hp hfp hgp hmass hx,
    radialTransport_cdf hD.le hn hω hf hg hp hfp hgp hmass hy]
  exact radialCDF_strictMonoOn hn hω hf hp hfp hx hy hxy

include hR in
lemma radialTransport_image :
    radialTransport (f := f) hD.le hn hω hg hp hgp '' Ioo 0 R = Ioo 0 D := by
  have he := (radialTransport_continuous hD.le hn hω hf hg hp hgp).continuousOn.image_Ioo_of_strictMonoOn hR.le
    (radialTransport_strictMonoOn hD hn hω hf hg hp hfp hgp hmass)
  simpa only [radialTransport_zero hD hn hω hg hp hgp,radialTransport_top hD hn hω hg hp hgp hmass] using he

lemma radialTransport_deriv_pos {r : ℝ} (hr : r ∈ Ioo 0 R) :
    0 < deriv (radialTransport (f := f) hD.le hn hω hg hp hgp) r := by
  rw [(radialTransport_hasDerivAt hD.le hn hω hf hg hp hfp hgp hmass hr).deriv]
  have ht := radialTransport_interior hD.le hn hω hf hg hp hfp hgp hmass hr
  exact div_pos
    (mul_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) hω) (pow_pos hr.1 _))
      (Real.rpow_pos_of_pos (hfp r hr) _))
    (mul_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) hω) (pow_pos ht.1 _))
      (Real.rpow_pos_of_pos (hgp _ ht) _))

lemma radialTransport_jacobian {r : ℝ} (hr : r ∈ Ioo 0 R) :
    deriv (radialTransport (f := f) hD.le hn hω hg hp hgp) r *
      (radialTransport (f := f) hD.le hn hω hg hp hgp r/r)^(n-1) =
      (f r)^p/(g (radialTransport (f := f) hD.le hn hω hg hp hgp r))^p := by
  rw [(radialTransport_hasDerivAt hD.le hn hω hf hg hp hfp hgp hmass hr).deriv]
  have ht := radialTransport_interior hD.le hn hω hf hg hp hfp hgp hmass hr
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hg0 := (Real.rpow_pos_of_pos (hgp _ ht) p).ne'
  rw [div_pow]
  field_simp [hn0,hω.ne',hr.1.ne',ht.1.ne']

lemma radialTransport_weighted_jacobian {r : ℝ} (hr : r ∈ Ioo 0 R) :
    deriv (radialTransport (f := f) hD.le hn hω hg hp hgp) r *
      ((n:ℝ)*ω*(radialTransport (f := f) hD.le hn hω hg hp hgp r)^(n-1)*
        (g (radialTransport (f := f) hD.le hn hω hg hp hgp r))^p) =
      (n:ℝ)*ω*r^(n-1)*(f r)^p := by
  rw [(radialTransport_hasDerivAt hD.le hn hω hf hg hp hfp hgp hmass hr).deriv]
  have ht := radialTransport_interior hD.le hn hω hf hg hp hfp hgp hmass hr
  apply div_mul_cancel₀
  exact ne_of_gt (mul_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) hω) (pow_pos ht.1 _))
    (Real.rpow_pos_of_pos (hgp _ ht) _))

include hR in

lemma radialTransport_moment (H : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioo 0 D, ENNReal.ofReal ((n:ℝ)*ω*s^(n-1)*(g s)^p)*H s =
    ∫⁻ r in Ioo 0 R, ENNReal.ofReal ((n:ℝ)*ω*r^(n-1)*(f r)^p)*
      H (radialTransport (f := f) hD.le hn hω hg hp hgp r) := by
  rw [←radialTransport_image hR hD hn hω hf hg hp hfp hgp hmass]
  rw [lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioo
    (fun r hr => (radialTransport_hasDerivAt hD.le hn hω hf hg hp hfp hgp hmass hr).differentiableAt.hasDerivAt.hasDerivWithinAt)
    ((radialTransport_strictMonoOn hD hn hω hf hg hp hfp hgp hmass).monotoneOn.mono Ioo_subset_Icc_self)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  rw [←mul_assoc,←ENNReal.ofReal_mul]
  · congr 2
    exact radialTransport_weighted_jacobian hD hn hω hf hg hp hfp hgp hmass hr
  · exact (radialTransport_deriv_pos hD hn hω hf hg hp hfp hgp hmass hr).le

end
end CAT0Fillings.RadialSobolev
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma ac_congr {f g : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (he : EqOn f g (uIcc a b)) : AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ,hδ,hh⟩ := hf ε hε
  refine ⟨δ,hδ,fun E hE hlen => ?_⟩
  have hs : (∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2)) =
      ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [he (hE.1 i hi).1,he (hE.1 i hi).2]
  rw [hs]
  exact hh E hE hlen

lemma ac_of_nonnegative_derivative {t t' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn t (Icc a b))
    (hd : ∀ r ∈ Ioo a b, HasDerivAt t (t' r) r)
    (hp : ∀ r ∈ Ioo a b, 0 ≤ t' r) : AbsolutelyContinuousOnInterval t a b := by
  have hi : IntervalIntegrable t' volume a b := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    · simpa only [uIcc_of_le hab] using hc
    · simpa only [min_eq_left hab,max_eq_right hab] using hd
    · simpa only [min_eq_left hab,max_eq_right hab] using hp
  have ha := hi.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hk : AbsolutelyContinuousOnInterval (fun _ : ℝ => t a) a b :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  apply ac_congr (ha.add hk)
  intro x hx
  rw [uIcc_of_le hab] at hx
  have hsub : uIcc a x ⊆ uIcc a b := by
    rw [uIcc_of_le hx.1,uIcc_of_le hab]
    exact Icc_subset_Icc_right hx.2
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    (hc.mono (Icc_subset_Icc_right hx.2))
    (fun r hr => hd r ⟨hr.1,hr.2.trans_le hx.2⟩) (hi.mono_set hsub)
  change (∫ r in a..x,t' r)+t a=t x
  rw [he,sub_add_cancel]

lemma lipschitz_power_ac {f : ℝ → ℝ} {K : ℝ≥0} {a b q : ℝ}
    (hf : LipschitzWith K f) (hq : 1 ≤ q) :
    AbsolutelyContinuousOnInterval (fun r => (f r)^q) a b := by
  obtain ⟨C,hC⟩ := isCompact_uIcc.bddBelow_image (hf.continuous.continuousOn (s := uIcc a b))
  obtain ⟨B,hB⟩ := isCompact_uIcc.bddAbove_image (hf.continuous.continuousOn (s := uIcc a b))
  have hp : ContDiffOn ℝ 1 (fun x : ℝ => x^q) (Icc C B) :=
    (Real.contDiff_rpow_const_of_le (by exact_mod_cast hq)).contDiffOn
  obtain ⟨L,hL⟩ := hp.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  have hrange : MapsTo f (uIcc a b) (Icc C B) := by
    intro x hx
    exact ⟨hC ⟨x,hx,rfl⟩,hB ⟨x,hx,rfl⟩⟩
  exact (hL.comp hf.lipschitzOnWith hrange).absolutelyContinuousOnInterval

lemma radial_agm {n : ℕ} (hn : 0 < n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (n:ℝ)*(a*b^(n-1))^((n:ℝ)⁻¹) ≤ a+((n:ℝ)-1)*b := by
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean2_weighted
    (show 0 ≤ (n:ℝ)⁻¹ by positivity)
    (show 0 ≤ ((n:ℝ)-1)/(n:ℝ) by positivity) ha hb
    (show (n:ℝ)⁻¹+((n:ℝ)-1)/(n:ℝ)=1 by field_simp; ring)
  rw [Real.mul_rpow ha (pow_nonneg hb _),←Real.rpow_natCast b (n-1),
    ←Real.rpow_mul hb] at *
  have he : ((n-1:ℕ):ℝ)*(n:ℝ)⁻¹ = ((n:ℝ)-1)/(n:ℝ) := by
    rw [Nat.cast_sub (by omega),Nat.cast_one,div_eq_mul_inv]
  rw [he]
  have hm := mul_le_mul_of_nonneg_left h hnR.le
  have heq : (n:ℝ)*((n:ℝ)⁻¹*a+((n:ℝ)-1)/(n:ℝ)*b) = a+((n:ℝ)-1)*b := by
    field_simp
  rw [heq] at hm
  exact hm

end CAT0Fillings.RadialSobolev
end

end OAI
