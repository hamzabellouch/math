import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeightReduction

namespace OAI

/-! Removing the finitely many rows above height one preserves the scalar
Eisenstein pole. The remaining positive kernel is the one used in the
Rankin integral of the square-integrable theta section. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaScalarHeightCutoff (p : ℂ × ℝ) (s : ℝ) : ℝ :=
  ∑' r : CubicThetaBottomRow,if r.height p≤1 then r.height p^s else 0

def cubicThetaScalarHeightHigh (p : ℂ × ℝ) (s : ℝ) : ℝ :=
  ∑' r : CubicThetaBottomRow,if 1<r.height p then r.height p^s else 0

lemma cubicThetaScalarHeightCutoff_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) :
    Summable (fun r : CubicThetaBottomRow => if r.height p≤1 then r.height p^s else 0) := by
  apply (cubicThetaScalarEisenstein_real_summable hp hs).of_nonneg_of_le
  · intro r
    split_ifs
    · exact Real.rpow_nonneg (r.height_pos hp).le _
    · exact le_rfl
  · intro r
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (r.height_pos hp).le _

lemma cubicThetaScalarHeightHigh_continuous {p : ℂ × ℝ} (hp : 0<p.2) :
    Continuous (cubicThetaScalarHeightHigh p) := by
  classical
  let S := (cubicThetaBottomRow_height_superlevel_finite hp zero_lt_one).toFinset
  have he (s : ℝ) : cubicThetaScalarHeightHigh p s=
      ∑ r∈S,if 1<r.height p then r.height p^s else 0 := by
    apply tsum_eq_sum
    intro r hr
    have hn : ¬1<r.height p := by
      intro hh
      exact hr (by change r∈(cubicThetaBottomRow_height_superlevel_finite hp zero_lt_one).toFinset
                   simpa using hh.le)
    simp only [ite_eq_right hn]
  rw [show cubicThetaScalarHeightHigh p=(fun s => ∑ r∈S,if 1<r.height p then r.height p^s else 0) from funext he]
  apply continuous_finsetSum
  intro r _
  by_cases hr : 1<r.height p
  · simp only [ite_eq_left hr]
    exact Real.continuous_const_rpow (r.height_pos hp).ne'
  · simp only [ite_eq_right hr]
    exact continuous_const

lemma cubicThetaScalarHeightHigh_summable {p : ℂ × ℝ} (hp : 0<p.2) (s : ℝ) :
    Summable (fun r : CubicThetaBottomRow => if 1<r.height p then r.height p^s else 0) := by
  apply summable_of_hasFiniteSupport
  apply (cubicThetaBottomRow_height_superlevel_finite hp zero_lt_one).subset
  intro r hr
  have hpos : 1<r.height p := by
    by_contra hn
    exact hr (ite_eq_right hn)
  exact hpos.le

lemma cubicThetaScalarHeightCutoff_split {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) :
    cubicThetaScalarHeightMass p s=
      cubicThetaScalarHeightCutoff p s+cubicThetaScalarHeightHigh p s := by
  rw [cubicThetaScalarHeightCutoff,cubicThetaScalarHeightHigh,
    ←(cubicThetaScalarHeightCutoff_summable hp hs).tsum_add
      (cubicThetaScalarHeightHigh_summable hp s)]
  apply tsum_congr
  intro r
  by_cases hr : r.height p≤1
  · simp only [ite_eq_left hr,ite_eq_right (not_lt.mpr hr),add_zero]
  · simp only [ite_eq_right hr,ite_eq_left (lt_of_not_ge hr),zero_add]

theorem cubicThetaScalarHeightCutoff_residue {p : ℂ × ℝ} (hp : 0<p.2) :
    Tendsto (fun s : ℝ => ((s-2:ℝ):ℂ)*(cubicThetaScalarHeightCutoff p s:ℂ))
      (𝓝[>] 2) (𝓝 ((Real.pi:ℂ)^2/(54*principalIdealZeta 2))) := by
  have hzero : Tendsto (fun s : ℝ => ((s-2:ℝ):ℂ)) (𝓝[>] 2) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℝ => ((s-2:ℝ):ℂ)) 2 := by fun_prop
    simpa only [sub_self,Complex.ofReal_zero] using h.tendsto.mono_left
      (show 𝓝[>] (2:ℝ)≤𝓝 2 from nhdsWithin_le_nhds)
  have hH := (Complex.continuous_ofReal.comp (cubicThetaScalarHeightHigh_continuous hp)).continuousAt.tendsto.mono_left
    (show 𝓝[>] (2:ℝ)≤𝓝 2 from nhdsWithin_le_nhds)
  have h := (cubicThetaScalarEisenstein_residue hp).sub (hzero.mul hH)
  simp only [zero_mul,sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [cubicThetaScalarEisenstein_ofReal hp,cubicThetaScalarHeightCutoff_split hp hs]
  dsimp only [Function.comp_apply]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
