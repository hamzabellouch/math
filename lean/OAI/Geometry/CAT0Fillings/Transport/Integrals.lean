import Mathlib
import OAI.Geometry.CAT0Fillings.Transport.RadialMoments

namespace OAI

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

lemma radialTransport_integral_moment_unscaled (H : ℝ → ℝ) :
    (∫ s in (0:ℝ)..D, s^(n-1)*(g s)^p*H s) =
    ∫ r in (0:ℝ)..R, r^(n-1)*(f r)^p*
      H (radialTransport (f := f) hD.le hn hω hg hp hgp r) := by
  apply mul_left_cancel₀ (ne_of_gt (mul_pos (Nat.cast_pos.mpr hn) hω))
  simpa only [←intervalIntegral.integral_const_mul,mul_assoc] using
    radialTransport_integral_moment hR hD hn hω hf hg hp hfp hgp hmass H

lemma radialTransport_integral_power (q : ℝ) :
    (∫ s in (0:ℝ)..D, s^(n-1)*(g s)^q) =
    ∫ r in (0:ℝ)..R, r^(n-1)*(f r)^p*
      (g (radialTransport (f := f) hD.le hn hω hg hp hgp r))^(q-p) := by
  rw [←radialTransport_integral_moment_unscaled hR hD hn hω hf hg hp hfp hgp hmass (fun s => (g s)^(q-p))]
  apply intervalIntegral.integral_congr_Ioo_of_le hD.le
  intro s hs
  dsimp only
  rw [mul_assoc,←Real.rpow_add (hgp s hs)]
  congr 2
  ring

end

lemma radial_divergence_algebra {n : ℕ} {r t d : ℝ} (hn : 2 ≤ n) (hr : r ≠ 0) :
    r^(n-1)*(d+(n-1:ℕ)*t/r) = (n-1:ℕ)*r^(n-2)*t+r^(n-1)*d := by
  have he : n-1 = n-2+1 := by omega
  rw [he,pow_succ]
  field_simp
  ring

lemma weighted_transport_derivative_integrable {n : ℕ} {f t : ℝ → ℝ} {R q : ℝ}
    (hR : 0 ≤ R) (hf : Continuous f) (hq : 0 ≤ q)
    (ht : AbsolutelyContinuousOnInterval t 0 R)
    (hdt : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ t r) :
    IntervalIntegrable (fun r => (f r)^q*
      (((n-1:ℕ):ℝ)*r^(n-2)*t r+r^(n-1)*deriv t r)) volume 0 R := by
  have hv : AbsolutelyContinuousOnInterval (fun r => r^(n-1)*t r) 0 R :=
    (contDiff_id.pow (n-1)).contDiffOn.absolutelyContinuousOnInterval.fun_mul ht
  have hh := hv.intervalIntegrable_deriv.continuousOn_mul
    (hf.rpow_const (fun _ => Or.inr hq)).continuousOn
  apply hh.congr_uIoo
  simp only [uIoo_of_le hR]
  intro r hr
  dsimp only
  rw [(weightedTransport_hasDerivAt (n := n) (hdt r hr).hasDerivAt).deriv]

lemma finite_transport_ibp {n : ℕ} {ω p q R D : ℝ} {f g : ℝ → ℝ} {K : ℝ≥0}
    (hR : 0 ≤ R) (hD : 0 < D) (hn : 2 ≤ n) (hω : 0 < ω)
    (hf : LipschitzWith K f) (hg : Continuous g) (hp : 0 < p) (hq : 1 ≤ q)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r, 0 < g r) (hfR : f R = 0)
    (hmass : radialCDF n ω f p R = radialCDF n ω g p D)
    (hexp : q+p/(n:ℝ)=p) :
    (n:ℝ)*(∫ s in (0:ℝ)..D,s^(n-1)*(g s)^q) ≤
      -q*∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(q-1)*deriv f r*
        radialTransport (f := f) hD.le (by omega : 0 < n) hω hg hp (fun r _ => hgp r) r := by
  have hn0 : 0 < n := by omega
  let t := radialTransport (f := f) hD.le hn0 hω hg hp (fun r _ => hgp r)
  have ht : Continuous t := radialTransport_continuous _ _ _ hf.continuous hg hp _
  have hta : AbsolutelyContinuousOnInterval t 0 R :=
    radialTransport_ac hR hD hn0 hω hf.continuous hg hp hfp (fun r _ => hgp r) hmass
  have hdt : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ t r := fun r hr =>
    (radialTransport_hasDerivAt hD.le hn0 hω hf.continuous hg hp hfp (fun r _ => hgp r) hmass hr).differentiableAt
  have hA := weighted_transport_derivative_integrable (n := n) hR hf.continuous (by linarith : 0 ≤ q) hta hdt
  have hJ : Continuous (fun r => r^(n-1)*(f r)^p*(g (t r))^(q-p)) :=
    ((continuous_id.pow _).mul (hf.continuous.rpow_const (fun _ => Or.inr hp.le))).mul
      ((hg.comp ht).rpow_const (fun r => Or.inl (hgp (t r)).ne'))
  rw [radialTransport_integral_power hR hD hn0 hω hf.continuous hg hp hfp (fun r _ => hgp r) hmass q,
    ←intervalIntegral.integral_const_mul]
  calc
    (∫ r in (0:ℝ)..R,(n:ℝ)*(r^(n-1)*(f r)^p*(g (t r))^(q-p))) ≤
        ∫ r in (0:ℝ)..R,(f r)^q*((n-1:ℕ)*r^(n-2)*t r+r^(n-1)*deriv t r) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hR
        (hJ.intervalIntegrable _ _ |>.const_mul _) hA
      intro r hr
      have hpos := radialTransport_deriv_pos hD hn0 hω hf.continuous hg hp hfp (fun r _ => hgp r) hmass hr
      have htp := radialTransport_interior hD.le hn0 hω hf.continuous hg hp hfp (fun r _ => hgp r) hmass hr
      have hagm := transport_pointwise_agm hn0 (hfp r hr) (hgp (t r)) hpos.le
        (div_nonneg htp.1.le hr.1.le) hexp
        (radialTransport_jacobian hD hn0 hω hf.continuous hg hp hfp (fun r _ => hgp r) hmass hr)
      have hh := mul_le_mul_of_nonneg_left hagm (pow_nonneg hr.1.le (n-1))
      have he := radial_divergence_algebra (t := t r) (d := deriv t r) hn hr.1.ne'
      change (n:ℝ)*(r^(n-1)*(f r)^p*(g (t r))^(q-p)) ≤ _
      calc
        _ = r^(n-1)*((n:ℝ)*(f r)^p*(g (t r))^(q-p)) := by ring
        _ ≤ r^(n-1)*((f r)^q*(deriv t r+(n-1:ℕ)*(t r/r))) := hh
        _ = (f r)^q*(r^(n-1)*(deriv t r+(n-1:ℕ)*t r/r)) := by ring
        _ = _ := by rw [he]
    _ = -q*∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(q-1)*deriv f r*t r :=
      radial_integration_by_parts hn hR hf hq hfR hta hdt

end CAT0Fillings.RadialSobolev
end

end OAI
