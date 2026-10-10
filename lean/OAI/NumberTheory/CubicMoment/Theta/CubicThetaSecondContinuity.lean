import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAxisDifferentials
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaJointRegularity

namespace OAI

/-! Continuity of the pure second derivatives of the actual series.
Only the diagonal coordinate derivatives used by the Laplacian occur. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaAxisSecond_continuousOn (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ)
    {U : Set (ℂ × ℝ)} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    ContinuousOn (cubicThetaAxisSecond k f) U := by
  intro p hp
  have hfp := hf.contDiffAt (hU.mem_nhds hp)
  have hd : ContDiffAt ℝ 1 (fun q => fderiv ℝ f q (cubicThetaAxisVector k)) p :=
    (hfp.fderiv_right (m:=1) (by norm_num)).clm_apply contDiffAt_const
  have hdd : ContDiffAt ℝ 0 (fun q => fderiv ℝ
      (fun y => fderiv ℝ f y (cubicThetaAxisVector k)) q (cubicThetaAxisVector k)) p :=
    (hd.fderiv_right (m:=0) (by norm_num)).clm_apply contDiffAt_const
  have he : cubicThetaAxisSecond k f=ᶠ[𝓝 p]
      (fun q => fderiv ℝ (fun y => fderiv ℝ f y (cubicThetaAxisVector k)) q (cubicThetaAxisVector k)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact cubicThetaAxisSecond_eq_fderiv k f (hf.contDiffAt (hU.mem_nhds hq))
  exact (hdd.continuousAt.congr_of_eventuallyEq he).continuousWithinAt

lemma cubicThetaEisenstein_axisSecond_sum (k : CubicThetaAxis) {s : ℂ} (hs : 2<s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaAxisSecond k (fun q => cubicThetaEisenstein q s) p=
      ∑' cd, cubicThetaAxisSecond k (fun q => cubicThetaEisensteinGridTerm cd q s) p := by
  have h := (cubicThetaEisensteinGrid_coordinate_derivs k s hs p.1.re p.1.im hp).2.1
  have he : (fun t => cubicThetaEisenstein (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t) s)=
      (fun t => ∑' cd, cubicThetaEisensteinGridTerm cd (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t) s) :=
    funext (fun t => cubicThetaEisenstein_eq_grid _ _)
  unfold cubicThetaAxisSecond
  rw [he]
  exact h

lemma cubicThetaEisensteinGrid_local_second_bound (k : CubicThetaAxis) (s : ℂ) (hs : 2<s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ∃ r : ℝ, 0<r ∧ ∃ u : Eisenstein × Eisenstein → ℝ, Summable u ∧
      ∀ cd q, q∈Metric.ball p r → 0<q.2 ∧
        ‖cubicThetaAxisSecond k (fun y => cubicThetaEisensteinGridTerm cd y s) q‖≤u cd := by
  let a := p.2/2
  let H := p.2*cubicThetaHeightConstant p+1
  have ha : 0<a := half_pos hp
  have hc : ContinuousAt (fun q : ℂ × ℝ => q.2*cubicThetaHeightConstant q) p := by
    unfold cubicThetaHeightConstant
    have hn : p.2^2≠0 := pow_ne_zero _ hp.ne'
    fun_prop
  have hU : {q : ℂ × ℝ | a<q.2 ∧ q.2*cubicThetaHeightConstant q<H}∈𝓝 p :=
    (continuous_snd.continuousAt.eventually_const_lt (by dsimp [a]; linarith)).and
      (hc.eventually_lt_const (by dsimp [H]; linarith))
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hU
  let u := fun cd => (H^s.re*(cubicThetaSecondJetConstant s/a^2))*cubicThetaGridDecay s cd
  refine ⟨r,hr,u,(cubicThetaGridDecay_summable hs).mul_left _,?_⟩
  intro cd q hq
  obtain ⟨haq,hH⟩ := hsub hq
  have hq0 := ha.trans haq
  refine ⟨hq0,?_⟩
  have hj := (cubicThetaEisensteinGrid_jetBound cd.1 cd.2 s q.1.re q.1.im hq0 k).2
  have haxis : cubicThetaAxisFunction
      (fun a b t => cubicThetaEisensteinGridTerm cd (cubicThetaCartesianPoint a b t) s)
      k q.1.re q.1.im q.2=(fun t => cubicThetaEisensteinGridTerm cd
        (cubicThetaCoordinateLine k q.1.re q.1.im q.2 t) s) := by
    cases k <;> rfl
  rw [haxis] at hj
  change ‖cubicThetaAxisSecond k (fun y => cubicThetaEisensteinGridTerm cd y s) q‖≤
    ‖cubicThetaEisensteinGridTerm cd (cubicThetaCartesianPoint q.1.re q.1.im q.2) s‖*
      (cubicThetaSecondJetConstant s/q.2^2) at hj
  rw [cubicThetaCartesianPoint_self] at hj
  have hf := cubicThetaEisensteinGridTerm_uniform_bound cd hq0 hs hH.le
  have hrat : cubicThetaSecondJetConstant s/q.2^2≤cubicThetaSecondJetConstant s/a^2 :=
    div_le_div_of_nonneg_left (cubicThetaJetConstants_nonneg s).2 (sq_pos_of_pos ha)
      (pow_le_pow_left₀ ha.le haq.le 2)
  calc
    _ ≤ ‖cubicThetaEisensteinGridTerm cd q s‖*(cubicThetaSecondJetConstant s/q.2^2) := hj
    _ ≤ (H^s.re*cubicThetaGridDecay s cd)*(cubicThetaSecondJetConstant s/a^2) :=
      mul_le_mul hf hrat (div_nonneg (cubicThetaJetConstants_nonneg s).2 (sq_nonneg _))
        ((_root_.norm_nonneg _).trans hf)
    _ = u cd := by dsimp [u]; ring

lemma cubicThetaEisenstein_axisSecond_continuous (k : CubicThetaAxis) {s : ℂ} (hs : 2<s.re) :
    ContinuousOn (cubicThetaAxisSecond k (fun q => cubicThetaEisenstein q s))
      {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨r,hr,u,hu,hb⟩ := cubicThetaEisensteinGrid_local_second_bound k s hs hp
  have hc : ContinuousOn (fun q => ∑' cd, cubicThetaAxisSecond k
      (fun y => cubicThetaEisensteinGridTerm cd y s) q) (Metric.ball p r) := by
    apply continuousOn_tsum _ hu (fun cd q hq => (hb cd q hq).2)
    intro cd
    apply (cubicThetaAxisSecond_continuousOn k (fun y => cubicThetaEisensteinGridTerm cd y s)
      (isOpen_lt continuous_const continuous_snd) (fun q hq =>
        ((cubicThetaEisensteinGridTerm_contDiffAt cd s hq).of_le
          (show (2:ℕ∞ω)≤∞ by norm_num)).contDiffWithinAt)).mono
    intro q hq
    exact (hb cd q hq).1
  have he : cubicThetaAxisSecond k (fun q => cubicThetaEisenstein q s)=ᶠ[𝓝 p]
      (fun q => ∑' cd, cubicThetaAxisSecond k (fun y => cubicThetaEisensteinGridTerm cd y s) q) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with q hq
    exact cubicThetaEisenstein_axisSecond_sum k hs hq
  exact ((hc.continuousAt (Metric.ball_mem_nhds p hr)).congr_of_eventuallyEq he).continuousWithinAt

end CubicFirstMoment

end

end OAI
