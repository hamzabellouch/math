import OAI.MeasureTheory.Falconer.Graphs.GraphCartesianSubstitution

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

theorem graphCartesianFrequency_contDiff : ContDiff ℝ ∞ graphCartesianFrequency := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ 0
  · exact contDiff_apply ℝ ℝ 1

theorem graphJacobianWeight_contDiffAt (x : GraphLiftSpace)
    (hx : graphCartesianFrequency x ≠ 0) : ContDiffAt ℝ ∞ graphJacobianWeight x := by
  have hr := graphCartesianFrequency_contDiff.contDiffAt.norm ℝ hx
  have hs : ContDiffAt ℝ ∞ (fun y : GraphLiftSpace => Real.sqrt (1+(y 2)^2)) x :=
    (contDiffAt_const.add ((contDiff_apply ℝ ℝ 2).contDiffAt.pow 2)).sqrt (by positivity)
  exact (hr.mul hs).inv (mul_ne_zero (norm_ne_zero_iff.mpr hx) (by positivity))

theorem graphLiftInverse_contDiffAt (q : GraphLiftSpace) (hq : q ∈ graphLiftStrip) :
    ContDiffAt ℝ ∞ graphLiftInverse q := by
  have hb := abs_lt.mp (show |q 1-q 2| < Real.pi from hq)
  have hcos : Real.cos ((q 1-q 2)/2) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hb.1],by linarith [hb.2]⟩).ne'
  have hd : ContDiffAt ℝ ∞ (fun y : GraphLiftSpace => (y 1-y 2)/2) q := by fun_prop
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [graphLiftInverse]
  · exact ((contDiffAt_const.mul (contDiff_apply ℝ ℝ 0).contDiffAt).mul
      (Real.contDiff_cos.contDiffAt.comp q hd))
  · fun_prop
  · change ContDiffAt ℝ ∞ (fun y : GraphLiftSpace => Real.tan ((y 1-y 2)/2)) q
    have ht : ContDiffAt ℝ ∞ Real.tan ((q 1-q 2)/2) := Real.contDiffAt_tan.mpr hcos
    have hcomp := ht.comp q hd
    exact hcomp

theorem graphJacobianWeight_uniform_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GraphLiftSpace, ‖x‖ ≤ 8 →
      1/8 ≤ ‖graphCartesianFrequency x‖ → ‖iteratedFDeriv ℝ n graphJacobianWeight x‖ ≤ C := by
  let K : Set GraphLiftSpace := closedBall 0 8 ∩ {x | 1/8 ≤ ‖graphCartesianFrequency x‖}
  have hK : IsCompact K := (isCompact_closedBall (0:GraphLiftSpace) 8).inter_right
    (isClosed_le continuous_const graphCartesianFrequency_contDiff.continuous.norm)
  have hc : ContinuousOn (iteratedFDeriv ℝ n graphJacobianWeight) K := by
    intro x hx
    have hr : 1/8 ≤ ‖graphCartesianFrequency x‖ := hx.2
    have hne : graphCartesianFrequency x ≠ 0 := norm_pos_iff.mp (by linarith)
    exact ((graphJacobianWeight_contDiffAt x hne).continuousAt_iteratedFDeriv
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro x hx hr
  exact (hC x ⟨by simpa only [mem_closedBall,dist_zero_right] using hx,hr⟩).trans (le_max_right _ _)

theorem graph_sign_cutoff_uniform_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Plane × Plane, ‖p‖ ≤ 2 →
      ‖iteratedFDeriv ℝ n graphSignPlus p‖ ≤ C ∧
      ‖iteratedFDeriv ℝ n graphSignMinus p‖ ≤ C := by
  have hp := graphSignPlus_contDiff.continuous_iteratedFDeriv (m := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hm := graphSignMinus_contDiff.continuous_iteratedFDeriv (m := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  obtain ⟨A,hA⟩ := (isCompact_closedBall (0:Plane × Plane) 2).exists_bound_of_continuousOn hp.continuousOn
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:Plane × Plane) 2).exists_bound_of_continuousOn hm.continuousOn
  refine ⟨max 0 (max A B),le_max_left _ _,?_⟩
  intro p hp
  have hmem : p ∈ closedBall (0:Plane × Plane) 2 := by simpa only [mem_closedBall,dist_zero_right] using hp
  exact ⟨(hA p hmem).trans ((le_max_left A B).trans (le_max_right _ _)),
    (hB p hmem).trans ((le_max_right A B).trans (le_max_right _ _))⟩

end PlanarFalconer

end OAI
