import OAI.Analysis.LienardCycles.ConditionalFit

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
noncomputable def angle (x : ℝ) : ℝ := (Real.log (1+x)-Real.log (1-x))/2

lemma angle_analytic {x : ℝ} (hx : |x| < 1) : ContDiffAt ℝ ω angle x := by
  have h := abs_lt.mp hx
  apply ContDiffAt.div_const
  apply ContDiffAt.sub
  · exact (contDiffAt_const.add contDiffAt_id).log (by dsimp only [id_eq]; linarith [h.1,h.2])
  · exact (contDiffAt_const.sub contDiffAt_id).log (by dsimp only [id_eq]; linarith [h.1,h.2])

lemma angle_deriv {x : ℝ} (hx : |x| < 1) : HasDerivAt angle (1/(1-x^2)) x := by
  have h := abs_lt.mp hx
  have h₁ : 1+x ≠ 0 := by linarith
  have h₂ : 1-x ≠ 0 := by linarith
  have h₃ : 1-x^2 ≠ 0 := by nlinarith [mul_pos (show 0 < 1+x by linarith) (show 0 < 1-x by linarith)]
  convert! (((hasDerivAt_id x).const_add 1).log h₁).sub
    (((hasDerivAt_id x).const_sub 1).log h₂) |>.div_const 2 using 1
  dsimp only [id_eq]
  field_simp [h₁,h₂,h₃]
  ring

@[simp] lemma angle_zero : angle 0=0 := by simp [angle]
lemma angle_neg (x : ℝ) : angle (-x) = -angle x := by
  simp only [angle,sub_neg_eq_add,←sub_eq_add_neg]
  ring

lemma angle_strictMono : StrictMonoOn angle (Ioo (-1) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (fun x hx => (angle_deriv (abs_lt.mpr hx)).continuousAt.continuousWithinAt)
  intro x hx
  have hx' := interior_subset (s := Ioo (-1) 1) hx
  rw [(angle_deriv (abs_lt.mpr hx')).deriv]
  exact div_pos one_pos (by nlinarith [mul_pos (sub_pos.mpr hx'.2) (show 0 < 1+x by linarith [hx'.1])])
end QuinticLienard

end OAI
