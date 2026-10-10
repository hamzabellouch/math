import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSpatialDerivativeBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSpatialContinuity
import Mathlib.Analysis.Calculus.SmoothSeries

namespace OAI

/-! Joint C1 regularity of the literal arithmetic Eisenstein series.
The locally uniform derivative majorant is proved from its actual rows. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma cubicThetaEisensteinGrid_local_fderiv_bound (s : ℂ) (hs : 2<s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ∃ r : ℝ, 0<r ∧ ∃ u : Eisenstein × Eisenstein → ℝ, Summable u ∧
      ∀ cd q, q∈Metric.ball p r → 0<q.2 ∧
        ‖fderiv ℝ (fun z => cubicThetaEisensteinGridTerm cd z s) q‖≤u cd := by
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
  let u := fun cd => (3*(H^s.re*(cubicThetaFirstJetConstant s/a)))*cubicThetaGridDecay s cd
  refine ⟨r,hr,u,(cubicThetaGridDecay_summable hs).mul_left _,?_⟩
  intro cd q hq
  obtain ⟨haq,hH⟩ := hsub hq
  have hq0 := ha.trans haq
  refine ⟨hq0,?_⟩
  have hf := cubicThetaEisensteinGridTerm_uniform_bound cd hq0 hs hH.le
  have hrat : cubicThetaFirstJetConstant s/q.2≤cubicThetaFirstJetConstant s/a :=
    div_le_div_of_nonneg_left (cubicThetaJetConstants_nonneg s).1 ha haq.le
  calc
    _ ≤ 3*(‖cubicThetaEisensteinGridTerm cd q s‖*(cubicThetaFirstJetConstant s/q.2)) :=
      cubicThetaEisensteinGridTerm_fderiv_bound cd s hq0
    _ ≤ 3*((H^s.re*cubicThetaGridDecay s cd)*(cubicThetaFirstJetConstant s/a)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hf hrat (div_nonneg (cubicThetaJetConstants_nonneg s).1 hq0.le)
          ((_root_.norm_nonneg _).trans hf)) (by norm_num)
    _ = u cd := by dsimp [u]; ring

theorem cubicThetaEisenstein_contDiffAt_one {s : ℂ} (hs : 2<s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q => cubicThetaEisenstein q s) p := by
  obtain ⟨r,hr,u,hu,hb⟩ := cubicThetaEisensteinGrid_local_fderiv_bound s hs hp
  let f := fun cd : Eisenstein × Eisenstein => fun q => cubicThetaEisensteinGridTerm cd q s
  let df := fun cd : Eisenstein × Eisenstein => fun q => fderiv ℝ (f cd) q
  have hdf cd q (hq : q∈Metric.ball p r) : HasFDerivAt (f cd) (df cd q) q :=
    ((cubicThetaEisensteinGridTerm_contDiffAt cd s (hb cd q hq).1).differentiableAt (by simp)).hasFDerivAt
  have hd q (hq : q∈Metric.ball p r) :
      HasFDerivAt (fun q => ∑' cd, f cd q) (∑' cd, df cd q) q :=
    hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball p r).isPreconnected
      hdf (fun cd q hq => (hb cd q hq).2) (Metric.mem_ball_self hr)
      (cubicThetaEisensteinGrid_summable hp hs) hq
  have hdc : ContinuousOn (fun q => ∑' cd, df cd q) (Metric.ball p r) := by
    apply continuousOn_tsum _ hu (fun cd q hq => (hb cd q hq).2)
    intro cd q hq
    exact ((cubicThetaEisensteinGridTerm_contDiffAt cd s (hb cd q hq).1).fderiv_right
      (m:=0) (by simp)).continuousAt.continuousWithinAt
  have hc : ContDiffOn ℝ 1 (fun q => ∑' cd, f cd q) (Metric.ball p r) := by
    rw [show (1:ℕ∞ω)=0+1 from rfl,contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
    refine ⟨fun q hq => (hd q hq).differentiableAt.differentiableWithinAt,by norm_num,?_⟩
    apply contDiffOn_zero.mpr
    exact hdc.congr (fun q hq => (hd q hq).fderiv)
  have he : (fun q => cubicThetaEisenstein q s)=(fun q => ∑' cd, f cd q) :=
    funext (fun q => cubicThetaEisenstein_eq_grid q s)
  rw [he]
  exact hc.contDiffAt (Metric.ball_mem_nhds p hr)

end CubicFirstMoment

end

end OAI
