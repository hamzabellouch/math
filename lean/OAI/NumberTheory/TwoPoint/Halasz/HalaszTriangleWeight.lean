import OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleZero
import Mathlib.Analysis.Fourier.PoissonSummation

namespace OAI

/-! A continuous compactly supported majorant of a dyadic interval.
The adjoining affine pieces have exactly the integrals already estimated. -/
namespace TwoPointCorrelations

open MeasureTheory

noncomputable def halaszTriangleWeight (N x : ℝ) : ℝ :=
  max 0 (min (2/N*x-1) (5-2/N*x))

lemma halasz_triangle_weight_nonneg (N x : ℝ) : 0 ≤ halaszTriangleWeight N x :=
  le_max_left _ _

lemma halasz_triangle_weight_le_two (N x : ℝ) : halaszTriangleWeight N x ≤ 2 := by
  unfold halaszTriangleWeight
  apply max_le (by norm_num)
  have h1 := min_le_left (2/N*x-1) (5-2/N*x)
  have h2 := min_le_right (2/N*x-1) (5-2/N*x)
  linarith

lemma halasz_triangle_weight_left_zero (N x : ℝ) (hN : 0 < N) (hx : x ≤ N/2) :
    halaszTriangleWeight N x = 0 := by
  unfold halaszTriangleWeight
  apply max_eq_left
  apply (min_le_left _ _).trans
  have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
  nlinarith

lemma halasz_triangle_weight_right_zero (N x : ℝ) (hN : 0 < N) (hx : 5*N/2 ≤ x) :
    halaszTriangleWeight N x = 0 := by
  unfold halaszTriangleWeight
  apply max_eq_left
  apply (min_le_right _ _).trans
  have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
  nlinarith

lemma halasz_triangle_weight_left (N x : ℝ) (hN : 0 < N)
    (hx : x ∈ Set.Icc (N/2) (3*N/2)) : halaszTriangleWeight N x = 2/N*x-1 := by
  unfold halaszTriangleWeight
  have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
  rw [min_eq_left (by nlinarith [hx.2]), max_eq_right (by nlinarith [hx.1])]

lemma halasz_triangle_weight_right (N x : ℝ) (hN : 0 < N)
    (hx : x ∈ Set.Icc (3*N/2) (5*N/2)) : halaszTriangleWeight N x = -(2/N)*x+5 := by
  unfold halaszTriangleWeight
  have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
  rw [min_eq_right (by nlinarith [hx.1]), max_eq_right (by nlinarith [hx.2])]
  ring

lemma halasz_triangle_weight_dyadic (N x : ℝ) (hN : 0 < N)
    (hx : x ∈ Set.Icc N (2*N)) : 1 ≤ halaszTriangleWeight N x := by
  unfold halaszTriangleWeight
  apply le_max_of_le_right
  apply le_min
  · have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
    nlinarith [hx.1]
  · have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
    nlinarith [hx.2]

noncomputable def halaszTriangleFunction (N u v x : ℝ) : ℂ :=
  (halaszTriangleWeight N x:ℂ)*halaszLogPhase u v x

lemma halasz_triangle_function_zero (N u v x : ℝ) (hN : 0 < N)
    (hx : x ∉ Set.Icc (N/2) (5*N/2)) : halaszTriangleFunction N u v x = 0 := by
  rw [Set.mem_Icc, not_and_or] at hx
  rcases hx with hx | hx
  · simp only [not_le] at hx
    simp only [halaszTriangleFunction, halasz_triangle_weight_left_zero N x hN hx.le,
      Complex.ofReal_zero, zero_mul]
  · simp only [not_le] at hx
    simp only [halaszTriangleFunction, halasz_triangle_weight_right_zero N x hN hx.le,
      Complex.ofReal_zero, zero_mul]

lemma halasz_triangle_function_continuous (N u v : ℝ) (hN : 0 < N) :
    Continuous (halaszTriangleFunction N u v) := by
  have hw : Continuous (halaszTriangleWeight N) := by unfold halaszTriangleWeight; fun_prop
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have he : halaszTriangleFunction N u v =ᶠ[nhds 0] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds (half_pos hN)] with x hx
      simp only [halaszTriangleFunction, halasz_triangle_weight_left_zero N x hN hx.le,
        Complex.ofReal_zero, zero_mul]
    exact he.continuousAt
  · exact (Complex.continuous_ofReal.comp hw).continuousAt.mul
      (halasz_log_phase_deriv u v x hx).continuousAt

lemma halasz_triangle_function_compact (N u v : ℝ) (hN : 0 < N) :
    HasCompactSupport (halaszTriangleFunction N u v) :=
  HasCompactSupport.intro isCompact_Icc (fun x hx => halasz_triangle_function_zero N u v x hN hx)

end TwoPointCorrelations

end OAI
