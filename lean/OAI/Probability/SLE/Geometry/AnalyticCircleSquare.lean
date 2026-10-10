import Mathlib

namespace OAI

/-! The square mean of a holomorphic function bounds its central value.
This is the local energy estimate needed for the first exterior coefficient. -/
noncomputable section
open Set Filter Metric Function Complex MeasureTheory InnerProductSpace Real
open scoped Topology

namespace SLEExactGauge

lemma circleAverage_norm_sq_ge {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : ContinuousOn f (sphere c |r|)) :
    ‖circleAverage f c r‖^2≤circleAverage (fun z => ‖f z‖^2) c r := by
  let a := circleAverage f c r
  let L : ℂ →L[ℝ] ℝ := innerSL ℝ a
  have hL : ContinuousOn (fun z => L (f z)) (sphere c |r|) := L.continuous.comp_continuousOn hf
  have hI := hf.circleIntegrable'
  have hN := (hf.norm.pow 2).circleIntegrable'
  have hLin : circleAverage (fun z => L (f z)) c r=‖a‖^2 := by
    have hh := L.circleAverage_comp_comm hI
    change circleAverage (fun z => L (f z)) c r=L a at hh
    rw [hh]
    exact real_inner_self_eq_norm_sq a
  have hleft : circleAverage (fun z => (2:ℝ)*L (f z)-‖a‖^2) c r=‖a‖^2 := by
    rw [circleAverage_fun_sub (hL.const_mul 2).circleIntegrable' (circleIntegrable_const (‖a‖^2) c r)]
    have hmul : circleAverage (fun z => (2:ℝ)*L (f z)) c r=
        2*circleAverage (fun z => L (f z)) c r := by
      simpa only [smul_eq_mul] using (circleAverage_fun_smul (a := (2:ℝ)) (f := fun z => L (f z)) (c := c) (R := r))
    rw [hmul,hLin,circleAverage_const]
    ring
  rw [←hleft]
  apply circleAverage_mono ((hL.const_mul 2).sub continuousOn_const).circleIntegrable' hN
  intro z _
  have hn := norm_sub_sq_real (f z) a
  have hp := sq_nonneg ‖f z-a‖
  have hLa : L (f z)=inner ℝ (f z) a := by
    change inner ℝ a (f z)=inner ℝ (f z) a
    exact real_inner_comm _ _
  dsimp only [Pi.sub_apply,Pi.pow_apply]
  rw [hLa]
  nlinarith

lemma analytic_circleAverage_norm_sq_ge {f : ℂ → ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0:ℂ) |r|)) :
    ‖f 0‖^2≤circleAverage (fun z => ‖f z‖^2) 0 r := by
  have hm : circleAverage f 0 r=f 0 :=
    (show HarmonicOnNhd f (closedBall (0:ℂ) |r|) from fun z hz => (hf z hz).harmonicAt).circleAverage_eq
  rw [←hm]
  exact circleAverage_norm_sq_ge (hf.continuousOn.mono sphere_subset_closedBall)

end SLEExactGauge

end

end OAI
