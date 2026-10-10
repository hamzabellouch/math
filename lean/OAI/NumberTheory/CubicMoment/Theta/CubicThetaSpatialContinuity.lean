import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGridMajorant

namespace OAI

/-! Joint spatial continuity of the actual Eisenstein sum, from its
uniform summable majorant on a positive-height neighborhood. -/
noncomputable section
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinTerm_continuousAt (r : CubicThetaBottomRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContinuousAt (fun q => cubicThetaEisensteinTerm r q s) p := by
  have hden : Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2≠0 := by
    intro h
    have he := r.height_pos hp
    simp [CubicThetaBottomRow.height,h] at he
  have hh : ContinuousAt (fun q => r.height q) p := by
    unfold CubicThetaBottomRow.height
    fun_prop
  have hpow : ContinuousAt (fun t : ℝ => (t:ℂ)^s) (r.height p) :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (r.height_pos hp).ne')
  exact continuousAt_const.mul (hpow.comp hh)

lemma cubicThetaEisensteinGridTerm_continuousAt (cd : Eisenstein × Eisenstein) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContinuousAt (fun q => cubicThetaEisensteinGridTerm cd q s) p := by
  by_cases hc : cubicThetaAdmissiblePair cd
  · have he : (fun q => cubicThetaEisensteinGridTerm cd q s)=
        (fun q => cubicThetaEisensteinTerm (cubicThetaBottomRowEquiv.symm ⟨cd,hc⟩) q s) :=
      funext (fun q => cubicThetaEisensteinGridTerm_admissible ⟨cd,hc⟩ q s)
    rw [he]
    exact cubicThetaEisensteinTerm_continuousAt _ s hp
  · simp only [cubicThetaEisensteinGridTerm,hc,ite_false]
    exact continuousAt_const

theorem cubicThetaEisenstein_continuousAt {s : ℂ} (hs : 2<s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContinuousAt (fun q => cubicThetaEisenstein q s) p := by
  let H := p.2*cubicThetaHeightConstant p+1
  let U : Set (ℂ × ℝ) := {q | 0<q.2 ∧ q.2*cubicThetaHeightConstant q<H}
  have hb : ContinuousAt (fun q : ℂ × ℝ => q.2*cubicThetaHeightConstant q) p := by
    unfold cubicThetaHeightConstant
    have hn : p.2^2≠0 := pow_ne_zero _ hp.ne'
    fun_prop
  have hU : U ∈ 𝓝 p :=
    (continuous_snd.continuousAt.eventually_const_lt hp).and
      (hb.eventually_lt_const (by dsimp [H]; linarith))
  have hsum := continuousOn_tsum
    (s:=U) (fun cd q hq => (cubicThetaEisensteinGridTerm_continuousAt cd s hq.1).continuousWithinAt)
    ((cubicThetaGridDecay_summable hs).mul_left (H^s.re))
    (fun cd q hq => cubicThetaEisensteinGridTerm_uniform_bound cd hq.1 hs hq.2.le)
  have he : (fun q : ℂ × ℝ => cubicThetaEisenstein q s)=
      (fun q => ∑' cd, cubicThetaEisensteinGridTerm cd q s) :=
    funext (fun q => cubicThetaEisenstein_eq_grid q s)
  rw [he]
  exact hsum.continuousAt hU

theorem cubicThetaEisenstein_continuousOn {s : ℂ} (hs : 2<s.re) :
    ContinuousOn (fun q => cubicThetaEisenstein q s) {p : ℂ × ℝ | 0<p.2} :=
  fun _ hp => (cubicThetaEisenstein_continuousAt hs hp).continuousWithinAt

end CubicFirstMoment

end

end OAI
