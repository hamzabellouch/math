import Mathlib
import OAI.Geometry.CAT0Fillings.Transport.AbsoluteContinuity

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma weightedTransport_hasDerivAt {n : ℕ} {t : ℝ → ℝ} {r d : ℝ}
    (ht : HasDerivAt t d r) :
    HasDerivAt (fun s => s^(n-1)*t s)
      (((n-1:ℕ):ℝ)*r^(n-2)*t r+r^(n-1)*d) r := by
  simpa [Nat.sub_sub] using ((hasDerivAt_id r).fun_pow (n-1)).fun_mul ht

lemma radial_integration_by_parts {n : ℕ} {f t : ℝ → ℝ} {K : ℝ≥0} {R q : ℝ}
    (hn : 2 ≤ n) (hR : 0 ≤ R) (hf : LipschitzWith K f) (hq : 1 ≤ q) (hfR : f R = 0)
    (ht : AbsolutelyContinuousOnInterval t 0 R)
    (hdt : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ t r) :
    (∫ r in (0:ℝ)..R, (f r)^q*
      (((n-1:ℕ):ℝ)*r^(n-2)*t r+r^(n-1)*deriv t r)) =
      -q*∫ r in (0:ℝ)..R, r^(n-1)*(f r)^(q-1)*deriv f r*t r := by
  have hu : AbsolutelyContinuousOnInterval (fun r => (f r)^q) 0 R := lipschitz_power_ac hf hq
  have hv : AbsolutelyContinuousOnInterval (fun r => r^(n-1)*t r) 0 R :=
    (contDiff_id.pow (n-1)).contDiffOn.absolutelyContinuousOnInterval.fun_mul ht
  have hparts := hu.integral_mul_deriv_eq_deriv_mul hv
  have hn0 : n-1 ≠ 0 := by omega
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
  have hboundary : (f R)^q*(R^(n-1)*t R)-(f 0)^q*((0:ℝ)^(n-1)*t 0)=0 := by
    simp [hfR,Real.zero_rpow hq0,zero_pow hn0]
  rw [hboundary,zero_sub] at hparts
  have hleft : (∫ r in (0:ℝ)..R, (f r)^q*deriv (fun s => s^(n-1)*t s) r) =
      ∫ r in (0:ℝ)..R,(f r)^q*(((n-1:ℕ):ℝ)*r^(n-2)*t r+r^(n-1)*deriv t r) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hR
    intro r hr
    dsimp only
    exact congrArg (fun z => (f r)^q*z)
      (weightedTransport_hasDerivAt (n := n) (hdt r hr).hasDerivAt).deriv
  rw [hleft] at hparts
  have hright : (∫ r in (0:ℝ)..R, deriv (fun s => (f s)^q) r*(r^(n-1)*t r)) =
      q*∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(q-1)*deriv f r*t r := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with r hr hmem
    rw [(hr.hasDerivAt.rpow_const (Or.inr hq)).deriv]
    ring
  rw [hright] at hparts
  simpa only [neg_mul] using hparts

lemma radialTransport_ac {n : ℕ} {ω p R D : ℝ} {f g : ℝ → ℝ}
    (hR : 0 ≤ R) (hD : 0 < D) (hn : 0 < n) (hω : 0 < ω)
    (hf : Continuous f) (hg : Continuous g) (hp : 0 < p)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r)
    (hmass : radialCDF n ω f p R = radialCDF n ω g p D) :
    AbsolutelyContinuousOnInterval (radialTransport (f := f) hD.le hn hω hg hp hgp) 0 R := by
  apply ac_of_nonnegative_derivative hR (radialTransport_continuous hD.le hn hω hf hg hp hgp).continuousOn
  · intro r hr
    exact (radialTransport_hasDerivAt hD.le hn hω hf hg hp hfp hgp hmass hr).differentiableAt.hasDerivAt
  · intro r hr
    exact (radialTransport_deriv_pos hD hn hω hf hg hp hfp hgp hmass hr).le

end CAT0Fillings.RadialSobolev
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

section
variable {n : ℕ} {ω p R D : ℝ} {f g : ℝ → ℝ}
  (hR : 0 ≤ R) (hD : 0 < D) (hn : 0 < n) (hω : 0 < ω)
  (hf : Continuous f) (hg : Continuous g) (hp : 0 < p)
  (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r)
  (hmass : radialCDF n ω f p R = radialCDF n ω g p D)

include hR hf hfp hmass

lemma radialTransport_integral_moment (H : ℝ → ℝ) :
    (∫ s in (0:ℝ)..D, (n:ℝ)*ω*s^(n-1)*(g s)^p*H s) =
    ∫ r in (0:ℝ)..R, (n:ℝ)*ω*r^(n-1)*(f r)^p*
      H (radialTransport (f := f) hD.le hn hω hg hp hgp r) := by
  let t := radialTransport (f := f) hD.le hn hω hg hp hgp
  have he : (∫ r in (0:ℝ)..R,
      ((n:ℝ)*ω*(t r)^(n-1)*(g (t r))^p*H (t r))*deriv t r) =
      ∫ s in t 0..t R, (n:ℝ)*ω*s^(n-1)*(g s)^p*H s := by
    apply intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (f := t) (f' := deriv t)
      (g := fun s => (n:ℝ)*ω*s^(n-1)*(g s)^p*H s)
    · exact (radialTransport_continuous hD.le hn hω hf hg hp hgp).continuousOn
    · simp only [min_eq_left hR,max_eq_right hR]
      intro r hr
      exact (radialTransport_hasDerivAt hD.le hn hω hf hg hp hfp hgp hmass hr).differentiableAt.hasDerivAt
    · simp only [min_eq_left hR,max_eq_right hR]
      exact fun r hr => (radialTransport_deriv_pos hD hn hω hf hg hp hfp hgp hmass hr).le
  change (∫ s in (0:ℝ)..D, _) = ∫ r in (0:ℝ)..R, _
  have ht0 : t 0 = 0 := radialTransport_zero hD hn hω hg hp hgp
  have htR : t R = D := radialTransport_top hD hn hω hg hp hgp hmass
  rw [ht0,htR] at he
  rw [←he]
  apply intervalIntegral.integral_congr_Ioo_of_le hR
  intro r hr
  dsimp only
  calc
    (n:ℝ)*ω*(t r)^(n-1)*(g (t r))^p*H (t r)*deriv t r =
        (deriv t r*((n:ℝ)*ω*(t r)^(n-1)*(g (t r))^p))*H (t r) := by ring
    _ = (n:ℝ)*ω*r^(n-1)*(f r)^p*H (t r) := by
      rw [radialTransport_weighted_jacobian hD hn hω hf hg hp hfp hgp hmass hr]

end

lemma transport_power_identity {a b p q m : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : q+p*m=p) : a^q*(a^p/b^p)^m = a^p*b^(q-p) := by
  rw [Real.div_rpow (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hb.le _),
    ←Real.rpow_mul ha.le,←Real.rpow_mul hb.le,←mul_div_assoc,←Real.rpow_add ha]
  rw [hm]
  have he : q-p = -(p*m) := by linarith
  rw [he,Real.rpow_neg hb.le,div_eq_mul_inv]

lemma transport_pointwise_agm {n : ℕ} {a b u v p q : ℝ}
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hq : q+p/(n:ℝ)=p) (hjac : u*v^(n-1)=a^p/b^p) :
    (n:ℝ)*a^p*b^(q-p) ≤ a^q*(u+(n-1:ℕ)*v) := by
  have h := mul_le_mul_of_nonneg_left (radial_agm hn hu hv) (Real.rpow_nonneg ha.le q)
  rw [hjac] at h
  have hid := transport_power_identity ha hb (m := 1/(n:ℝ)) (by simpa only [mul_one_div] using hq)
  simp only [one_div] at hid
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  nlinarith [hid]

end CAT0Fillings.RadialSobolev

end

end OAI
