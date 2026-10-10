import Mathlib
import OAI.Analysis.Conductivity.Branching.CrossingBlock

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma crossing_uniform_ellipticity {M L : ℝ} (hM0 : 1 ≤ M) (hL : 1 ≤ L)
    (hM : ∀ x : ℝ, |deriv smoothTransition x| ≤ M ∧
      |deriv (deriv smoothTransition) x| ≤ M)
    (hsmall : 40*M*exp (-L) ≤ 1/56) (z x y X Y : ℝ) :
    (1/8)*(X^2+Y^2) ≤ crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ∧
    crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ≤ 10*(X^2+Y^2) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hε : 0 ≤ 40*M*exp (-L) := by positivity
  obtain ⟨hr₁,hr₂⟩ := crossing_residual_bounds hM0 hL hM z
  by_cases hz : z ≤ 0
  · obtain ⟨hyy,hxy⟩ := crossing_corrections_left hLp hz x y
    have hratio := (crossing_mode_ratios (L := L) (z := z)).1 hz
    have hα : |crossingResidualSecond L z/(exp (-3*z)*(1:ℝ)^2)| ≤ 40*M*exp (-L) := by
      simpa only [one_pow,mul_one] using hr₂
    obtain ⟨ha,hb⟩ := crossing_coefficients_small (exp_pos _).ne' (by norm_num : (1:ℝ)≠0)
      (by norm_num : (2:ℝ)≠0) hα hratio (by norm_num : |(1:ℝ)/2|≤2) x y
    rw [hyy,hxy]
    exact crossing_quadratic_ellipticity (a := 9) (b := 1/4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε hsmall ha hb X Y
  · have hz' : 0 ≤ z := le_of_not_ge hz
    obtain ⟨hxx,hxy⟩ := crossing_corrections_right hLp hz' x y
    have hratio := (crossing_mode_ratios (L := L) (z := z)).2 hz'
    have heq : crossingResidualFirst L z/(exp (-z)*(2:ℝ)^2) =
        (crossingResidualFirst L z/exp (-z))/4 := by ring
    have hα : |crossingResidualFirst L z/(exp (-z)*(2:ℝ)^2)| ≤ 40*M*exp (-L) := by
      rw [heq,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
      exact (div_le_iff₀ (by norm_num : (0:ℝ)<4)).mpr (by linarith)
    obtain ⟨ha,hb⟩ := crossing_coefficients_small (exp_pos _).ne' (by norm_num : (2:ℝ)≠0)
      (by norm_num : (1:ℝ)≠0) hα hratio (by norm_num : |(2:ℝ)/1|≤2) y x
    have hh := crossing_quadratic_ellipticity (a := 1/4) (b := 9)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε hsmall ha hb Y X
    rw [hxx,hxy]
    dsimp only [crossingYY]
    constructor <;> nlinarith [hh.1,hh.2]

theorem exists_elliptic_crossing : ∃ L : ℝ, 1 ≤ L ∧ ∀ z x y X Y : ℝ,
    (1/8)*(X^2+Y^2) ≤ crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ∧
    crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ≤ 10*(X^2+Y^2) := by
  obtain ⟨M,hM0,hM⟩ := exists_transition_derivative_bound
  obtain ⟨L,hL,hs⟩ := exists_small_crossing_scale hM0
  exact ⟨L,hL,crossing_uniform_ellipticity hM0 hL hM hs⟩

end ScalarConductivity

end

end OAI
