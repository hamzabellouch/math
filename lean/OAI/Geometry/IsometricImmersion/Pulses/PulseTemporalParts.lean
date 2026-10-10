import OAI.Geometry.IsometricImmersion.Pulses.PulseSpatialParts

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem pulseSpatialTest_partial_time (a tau : ℝ) (p : Coord) :
    coordPartial 1 (pulseSpatialTest a tau) p = 0 := by
  have hψ := ((pulseTest_contDiff a tau).differentiable (by simp) (p 0)).hasDerivAt
  have hproj : HasFDerivAt (fun q : Coord => q 0) (ContinuousLinearMap.proj 0) p :=
    (ContinuousLinearMap.proj 0 : Coord →L[ℝ] ℝ).hasFDerivAt
  have hh := hψ.comp_hasFDerivAt p hproj
  change fderiv ℝ ((pulseTest a tau) ∘ (fun q : Coord => q 0)) p (Pi.single 1 1) = 0
  rw [hh.fderiv]
  simp [smul_apply,ContinuousLinearMap.proj_apply]

theorem rectangleIntegral_partial_time_boundary {l r b t : ℝ}
    {f : Coord → ℝ} {U : Set Coord}
    (hlr : l ≤ r) (hbt : b ≤ t) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hbox : closedRectangle l r b t ⊆ U) :
    rectangleIntegral l r b t (coordPartial 1 f) =
      (∫ x in l..r, f (boxPoint x t)) - (∫ x in l..r, f (boxPoint x b)) := by
  rw [rectangleIntegral_swap hlr hbt ((partial_contDiffOn hf hU 1).continuousOn.mono hbox)]
  have hinner (x : ℝ) (hx : x ∈ Icc l r) :
      (∫ theta in b..t, coordPartial 1 f (boxPoint x theta)) =
        f (boxPoint x t)-f (boxPoint x b) := by
    have hcont : ContinuousOn (fun theta => coordPartial 1 f (boxPoint x theta)) (uIcc b t) := by
      rw [uIcc_of_le hbt]
      exact (partial_contDiffOn hf hU 1).continuousOn.comp
        (by unfold boxPoint; fun_prop) (fun theta htheta => hbox (boxPoint_mem hx htheta))
    have hderiv (theta : ℝ) (htheta : theta ∈ uIcc b t) :
        HasDerivAt (fun s => f (boxPoint x s)) (coordPartial 1 f (boxPoint x theta)) theta := by
      have hp : boxPoint x theta ∈ U := hbox (boxPoint_mem hx
        (by simpa only [uIcc_of_le hbt] using htheta))
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      exact hd.hasFDerivAt.comp_hasDerivAt theta (boxPoint_hasDerivAt_s x theta)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have htcont : ContinuousOn (fun x => f (boxPoint x t)) (uIcc l r) := by
    rw [uIcc_of_le hlr]
    exact hf.continuousOn.comp (by unfold boxPoint; fun_prop)
      (fun x hx => hbox (boxPoint_mem hx ⟨hbt,le_rfl⟩))
  have hbcont : ContinuousOn (fun x => f (boxPoint x b)) (uIcc l r) := by
    rw [uIcc_of_le hlr]
    exact hf.continuousOn.comp (by unfold boxPoint; fun_prop)
      (fun x hx => hbox (boxPoint_mem hx ⟨le_rfl,hbt⟩))
  calc
    _ = ∫ x in l..r, (f (boxPoint x t)-f (boxPoint x b)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hinner x (by simpa only [uIcc_of_le hlr] using hx)
    _ = _ := intervalIntegral.integral_sub htcont.intervalIntegrable hbcont.intervalIntegrable

theorem pulse_temporal_flux_partial {a tau : ℝ} {v : Coord → ℝ} {U : Set Coord}
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    coordPartial 1 (fun q => pulseSpatialTest a tau q*coordPartial 1 v q) p =
      pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p := by
  have hψ := (pulseSpatialTest_contDiff a tau).differentiable (by simp) p
  have hvt := ((partial_contDiffOn hv hU 1).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  rw [HessianCalculus.coordPartial_mul_at hψ hvt 1,pulseSpatialTest_partial_time]
  ring

theorem pulse_temporal_second_parts {a delta tau : ℝ}
    {v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U) :
    rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p) =
      (∫ x in (-a)..a, pulseTest a tau x*coordPartial 1 v (boxPoint x (delta/tau))) -
        (∫ x in (-a)..a, pulseTest a tau x*coordPartial 1 v (boxPoint x (-(delta/tau)))) := by
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hflux : ContDiffOn ℝ ∞ (fun p => pulseSpatialTest a tau p*coordPartial 1 v p) U :=
    (pulseSpatialTest_contDiff a tau).contDiffOn.mul (partial_contDiffOn hv hU 1)
  have hFTC := rectangleIntegral_partial_time_boundary hlr hbt hU hflux hSU
  have heq := rectangleIntegral_congr hlr hbt
    (fun p hp => pulse_temporal_flux_partial (a := a) (tau := tau) hv hU (hSU hp))
  rw [heq] at hFTC
  simpa only [pulseSpatialTest,pulse_boxPoint_zero] using hFTC

theorem pulse_temporal_second_parts_zero_initial {a delta tau : ℝ}
    {v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hinitial : ∀ x ∈ Icc (-a) a, coordPartial 1 v (boxPoint x (-(delta/tau))) = 0) :
    rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p) =
      ∫ x in (-a)..a, pulseTest a tau x*coordPartial 1 v (boxPoint x (delta/tau)) := by
  rw [pulse_temporal_second_parts ha hd ht hv hU hSU]
  have hzero : (∫ x in (-a)..a, pulseTest a tau x*coordPartial 1 v (boxPoint x (-(delta/tau)))) = 0 := by
    calc
      _ = ∫ _x in (-a)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rw [hinitial x (by simpa only [uIcc_of_le (by linarith : -a ≤ a)] using hx),mul_zero]
      _ = 0 := intervalIntegral.integral_zero
  rw [hzero,sub_zero]

end SmoothLocal.Pulse

end

end OAI
