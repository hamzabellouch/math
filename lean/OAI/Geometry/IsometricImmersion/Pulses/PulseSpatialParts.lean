import OAI.Geometry.IsometricImmersion.Pulses.PulseTestEnergy

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem pulse_boxPoint_zero (x t : ℝ) : boxPoint x t 0 = x := by
  change x*1+t*0=x
  ring

theorem pulse_boxPoint_one (x t : ℝ) : boxPoint x t 1 = t := by
  change x*0+t*1=t
  ring

def pulseSpatialTest (a tau : ℝ) (p : Coord) : ℝ := pulseTest a tau (p 0)

theorem pulseSpatialTest_contDiff (a tau : ℝ) : ContDiff ℝ ∞ (pulseSpatialTest a tau) :=
  (pulseTest_contDiff a tau).comp (contDiff_apply ℝ ℝ 0)

theorem pulseSpatialTest_partial (a tau : ℝ) (p : Coord) :
    coordPartial 0 (pulseSpatialTest a tau) p = deriv (pulseTest a tau) (p 0) := by
  have hψ := ((pulseTest_contDiff a tau).differentiable (by simp) (p 0)).hasDerivAt
  have hproj : HasFDerivAt (fun q : Coord => q 0) (ContinuousLinearMap.proj 0) p :=
    (ContinuousLinearMap.proj 0 : Coord →L[ℝ] ℝ).hasFDerivAt
  have hh := hψ.comp_hasFDerivAt p hproj
  change fderiv ℝ ((pulseTest a tau) ∘ (fun q : Coord => q 0)) p (Pi.single 0 1) = _
  rw [hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.proj_apply,Pi.single_eq_same,smul_eq_mul,mul_one]

theorem rectangleIntegral_eq_Icc_slices (f : Coord → ℝ) {l r b t : ℝ}
    (hlr : l ≤ r) (hbt : b ≤ t) :
    rectangleIntegral l r b t f = ∫ theta in Icc b t, ∫ x in Icc l r, f (boxPoint x theta) := by
  unfold rectangleIntegral
  rw [intervalIntegral.integral_of_le hbt,←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro theta htheta
  dsimp only
  rw [intervalIntegral.integral_of_le hlr,←integral_Icc_eq_integral_Ioc]

theorem pulse_spatial_flux_partial (i : Fin 2) {a tau : ℝ}
    {S v : Coord → ℝ} {U : Set Coord}
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) :
    coordPartial 0 (fun q => pulseSpatialTest a tau q*S q*coordPartial i v q) p =
      deriv (pulseTest a tau) (p 0)*S p*coordPartial i v p+
      pulseSpatialTest a tau p*coordPartial 0 S p*coordPartial i v p+
      pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial i v) p := by
  have hψ := (pulseSpatialTest_contDiff a tau).differentiable (by simp) p
  have hSd := (hS.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hvid := ((partial_contDiffOn hv hU i).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have houter := HessianCalculus.coordPartial_mul_at (hψ.mul hSd) hvid 0
  dsimp only [Pi.mul_apply] at houter
  have hinner := HessianCalculus.coordPartial_mul_at hψ hSd 0
  change coordPartial 0 (pulseSpatialTest a tau * S) p = _ at hinner
  rw [houter,hinner,pulseSpatialTest_partial]
  ring

theorem pulse_spatial_second_parts (i : Fin 2) {a delta tau : ℝ}
    {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U)
    (hSU : pulseStrip a delta tau ⊆ U) :
    rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial i v) p) =
      -rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => deriv (pulseTest a tau) (p 0)*S p*coordPartial i v p)-
       rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*coordPartial 0 S p*coordPartial i v p) := by
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hψ : ContDiffOn ℝ ∞ (pulseSpatialTest a tau) U := (pulseSpatialTest_contDiff a tau).contDiffOn
  have hψ' : ContDiffOn ℝ ∞ (fun p : Coord => deriv (pulseTest a tau) (p 0)) U :=
    ((contDiff_infty_iff_deriv.mp (pulseTest_contDiff a tau)).2.comp (contDiff_apply ℝ ℝ 0)).contDiffOn
  have hvi := partial_contDiffOn hv hU i
  have hflux : ContDiffOn ℝ ∞ (fun p => pulseSpatialTest a tau p*S p*coordPartial i v p) U :=
    (hψ.mul hS).mul hvi
  have hminus : axisBump a (-a) = 0 := axisBump_zero ha.le (by simp [abs_of_pos ha])
  have hplus : axisBump a a = 0 := axisBump_zero ha.le (by simp [abs_of_pos ha])
  have hedge : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      (pulseSpatialTest a tau (boxPoint (-a) theta)*S (boxPoint (-a) theta)*
        coordPartial i v (boxPoint (-a) theta)) = 0 ∧
      (pulseSpatialTest a tau (boxPoint a theta)*S (boxPoint a theta)*
        coordPartial i v (boxPoint a theta)) = 0 := by
    intro theta htheta
    simp only [pulseSpatialTest,pulseTest,pulse_boxPoint_zero,hminus,hplus,zero_mul,and_self]
  have hzero := rectangleIntegral_partial_t_zero hlr hbt hU hflux hSU hedge
  have heq := rectangleIntegral_congr hlr hbt
    (fun p hp => pulse_spatial_flux_partial i (a := a) (tau := tau) hS hv hU (hSU hp))
  rw [heq] at hzero
  have h1 := ((hψ'.mul hS).mul hvi).continuousOn.mono hSU
  have h2 := ((hψ.mul (partial_contDiffOn hS hU 0)).mul hvi).continuousOn.mono hSU
  have h3 := ((hψ.mul hS).mul (partial_contDiffOn hvi hU 0)).continuousOn.mono hSU
  rw [rectangleIntegral_add (f := fun p => deriv (pulseTest a tau) (p 0)*S p*coordPartial i v p+
      pulseSpatialTest a tau p*coordPartial 0 S p*coordPartial i v p)
      (g := fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial i v) p)
      hlr hbt (h1.add h2) h3,
    rectangleIntegral_add hlr hbt h1 h2] at hzero
  linarith

theorem pulse_spatial_second_cost (i : Fin 2) {a delta tau S0 S1 M : ℝ} {N : ℕ}
    {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hS0 : 0 ≤ S0) (hS1 : 0 ≤ S1) (hM : 0 ≤ M)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U)
    (hSU : pulseStrip a delta tau ⊆ U)
    (hSB : ∀ p ∈ pulseStrip a delta tau, |S p| ≤ S0)
    (hS1B : ∀ p ∈ pulseStrip a delta tau, |coordPartial 0 S p| ≤ S1)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ M*delta*tau/tau^N) :
    |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial i v) p)| ≤
      (2*pulseTestDerivativeBound a ha*S0*Real.sqrt (2*a)*M)*delta^2*tau/tau^N+
        (2*axisBumpDerivativeBound a ha 0*S1*Real.sqrt (2*a)*M)*delta^2/tau^N := by
  have htpos := zero_lt_one.trans_le ht
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd htpos.le]
  have hfirst := pulse_derivative_pairing_delta_sq i ha hd ht hS0 hM hU hSU hS hv hSB hL2
  have hsecond := pulse_test_pairing_extra_inv_tau i ha hd ht hS1 hM hU hSU
    (partial_contDiffOn hS hU 0) hv hS1B hL2
  have hfirst' : |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => deriv (pulseTest a tau) (p 0)*S p*coordPartial i v p)| ≤
      (2*pulseTestDerivativeBound a ha*S0*Real.sqrt (2*a)*M)*delta^2*tau/tau^N := by
    rw [rectangleIntegral_eq_Icc_slices _ hlr hbt]
    simpa only [pulse_boxPoint_zero] using hfirst
  have hsecond' : |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*coordPartial 0 S p*coordPartial i v p)| ≤
      (2*axisBumpDerivativeBound a ha 0*S1*Real.sqrt (2*a)*M)*delta^2/tau^N := by
    rw [rectangleIntegral_eq_Icc_slices _ hlr hbt]
    simpa only [pulseSpatialTest,pulse_boxPoint_zero] using hsecond
  rw [pulse_spatial_second_parts i ha hd htpos hS hv hU hSU]
  exact ((abs_sub _ _).trans (add_le_add (by simpa only [abs_neg] using hfirst') hsecond'))

end SmoothLocal.Pulse

end

end OAI
