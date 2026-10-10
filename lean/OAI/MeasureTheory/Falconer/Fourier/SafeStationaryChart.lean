import OAI.MeasureTheory.Falconer.Fourier.JointStationaryGeometry

namespace OAI

/-! # A global smooth extension of the fixed local stationary chart

The extension equals the actual chart near every direction in the support
of the fixed patch mask. It exists only to express its finite derivatives
as globally smooth separated factors; the stationary coefficients remain
the original coefficients.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

noncomputable def stationaryExtensionBump {n : ℕ} (c : Space n) : ContDiffBump c where
  rIn := 1/2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

noncomputable def stationarySafePoint {n : ℕ} (c x : Space n) : Space n :=
  c+(stationaryExtensionBump c x) • (x-c)

theorem stationarySafePoint_contDiff {n : ℕ} (c : Space n) :
    ContDiff ℝ ∞ (stationarySafePoint c) :=
  contDiff_const.add ((stationaryExtensionBump c).contDiff.smul
    (contDiff_id.sub contDiff_const))

theorem stationarySafePoint_near {n : ℕ} (c x : Space n) (hx : ‖x-c‖ ≤ 1/2) :
    stationarySafePoint c x = x := by
  have hb : stationaryExtensionBump c x = 1 :=
    (stationaryExtensionBump c).one_of_mem_closedBall (by
      simpa only [mem_closedBall,dist_eq_norm,stationaryExtensionBump] using hx)
  simp only [stationarySafePoint,hb,one_smul,add_sub_cancel]

theorem stationarySafePoint_bound {n : ℕ} (c x : Space n) :
    ‖stationarySafePoint c x-c‖ ≤ 1 := by
  by_cases hb : stationaryExtensionBump c x = 0
  · simp only [stationarySafePoint,hb,zero_smul,add_zero,sub_self,norm_zero]
    norm_num
  · have hx : ‖x-c‖ < 1 := by
      have hs : x ∈ Function.support (stationaryExtensionBump c) := hb
      rw [(stationaryExtensionBump c).support_eq] at hs
      simpa only [stationaryExtensionBump,mem_ball,dist_eq_norm] using hs
    simp only [stationarySafePoint,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (stationaryExtensionBump c).nonneg]
    calc
      _ ≤ 1*‖x-c‖ := mul_le_mul_of_nonneg_right (stationaryExtensionBump c).le_one (norm_nonneg _)
      _ ≤ 1 := by simpa using hx.le

theorem stationarySafePoint_nonantipodal (m : ℕ) (e : Space (m+3)) :
    (gnomonicChart (0 : Space (m+2)) : Space (m+3))+
      stationarySafePoint (gnomonicChart (0 : Space (m+2))) e ≠ 0 := by
  intro he
  have hbound := stationarySafePoint_bound
    (gnomonicChart (0 : Space (m+2)) : Space (m+3)) e
  have hv : stationarySafePoint (gnomonicChart (0 : Space (m+2))) e =
      -(gnomonicChart (0 : Space (m+2)) : Space (m+3)) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using he
  rw [hv,norm_sub_rev,sub_neg_eq_add,← two_smul ℝ,norm_smul,sphere_norm] at hbound
  norm_num at hbound

noncomputable def safeStationaryChart (m : ℕ)
    (z : Space (m+3) × Space (m+2)) : Space (m+3) :=
  jointStationaryChart m
    (stationarySafePoint (gnomonicChart (0 : Space (m+2))) z.1,
      stationarySafePoint 0 z.2)

theorem safeStationaryChart_contDiff (m : ℕ) : ContDiff ℝ ∞ (safeStationaryChart m) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  let g : Space (m+3) × Space (m+2) → Space (m+3) × Space (m+2) := fun q =>
    (stationarySafePoint (gnomonicChart (0 : Space (m+2))) q.1,stationarySafePoint 0 q.2)
  have hg : ContDiff ℝ ∞ g :=
    ((stationarySafePoint_contDiff _).comp contDiff_fst).prodMk
      ((stationarySafePoint_contDiff _).comp contDiff_snd)
  have hu : ‖stationarySafePoint (0 : Space (m+2)) z.2‖ < 2 := by
    have h := stationarySafePoint_bound (0 : Space (m+2)) z.2
    rw [sub_zero] at h
    linarith
  have hz : g z ∈ jointStationaryRegion m :=
    ⟨stationarySafePoint_nonantipodal m z.1,hu⟩
  change ContDiffAt ℝ ∞ (jointStationaryChart m ∘ g) z
  exact (jointStationaryChart_contDiffAt m hz).comp z hg.contDiffAt

theorem safeStationaryChart_zero (m : ℕ) (e : Sphere (m+3))
    (he : ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2) :
    safeStationaryChart m (e,0) = (e : Space (m+3)) := by
  have hu : ‖(0 : Space (m+2))-0‖ ≤ (1 : ℝ)/2 := by norm_num
  have hq : quadraticSpherePoint (0 : Space (m+2)) =
      (gnomonicChart (0 : Space (m+2)) : Space (m+3)) := by
    simpa [quadraticToGnomonic] using
      (gnomonicChart_quadraticToGnomonic (u := (0 : Space (m+2))) (by simp)).symm
  simp only [safeStationaryChart,jointStationaryChart,stationarySafePoint_near _ _ he,
    stationarySafePoint_near _ _ hu,hq,← stationaryPoleRotation_apply,stationaryPoleRotation_pole]

noncomputable def safeStationaryDensity (m : ℕ) (u : Space (m+2)) : ℂ :=
  quadraticChartDensity m (stationarySafePoint 0 u)

theorem safeStationaryDensity_contDiff (m : ℕ) :
    ContDiff ℝ ∞ (safeStationaryDensity m) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have hu : ‖stationarySafePoint (0 : Space (m+2)) u‖ < 2 := by
    have h := stationarySafePoint_bound (0 : Space (m+2)) u
    rw [sub_zero] at h
    linarith
  exact (quadraticChartDensity_contDiffAt m hu).comp u
    (stationarySafePoint_contDiff _).contDiffAt

theorem maskedStationaryCoefficient_safe (m j : ℕ) (B : Space (m+3) → ℂ)
    (e : Space (m+3)) :
    maskedStationaryCoefficient m j B e = (stationaryPatchMask m e : ℂ)*
      quadraticJetCoefficient j (fun u => safeStationaryDensity m u*B (safeStationaryChart m (e,u))) := by
  by_cases he : stationaryPatchMask m e = 0
  · simp only [maskedStationaryCoefficient,he,Complex.ofReal_zero,zero_mul]
  · have hep : ‖e-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2 := by
      exact (poleCutoff_support _ _ he).le.trans (by norm_num)
    unfold maskedStationaryCoefficient actualStationaryCoefficient
    congr 1
    apply quadraticJetCoefficient_congr
    filter_upwards [isOpen_ball.mem_nhds (show (0 : Space (m+2)) ∈ ball 0 (1/2) by
      simp only [mem_ball,dist_self]; norm_num)] with u hu
    have hu' : ‖u-(0 : Space (m+2))‖ ≤ 1/2 := by
      exact (mem_ball_iff_norm.mp hu).le
    simp only [safeStationaryDensity,safeStationaryChart,jointStationaryChart,
      stationarySafePoint_near _ e hep,stationarySafePoint_near _ u hu',
      unmaskedStationaryAmplitude,quadraticChartDensity]

end Falconer

end OAI
