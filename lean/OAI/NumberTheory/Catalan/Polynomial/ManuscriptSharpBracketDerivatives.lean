import OAI.NumberTheory.Catalan.Estimates.ManuscriptSharpDerivativeBounds

namespace OAI

section

noncomputable section
namespace InternalCatalan.ManuscriptSharpHeight
open Set

theorem case1_X_closed_bracket_deriv_abs_lt (m : ℤ)
    (hm : m ∈ barrierCase1XBrackets) {x : ℝ}
    (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    |deriv barrierCase1X x| < 12852 := by
  obtain ⟨hdom, hzero, hone⟩ := Case1Height.X_closed_bracket_margins m hm hx
  have hmargin : (7 / 10000 : ℝ) ≤ 1 / 100 := by norm_num
  exact case1_X_deriv_abs_lt hdom (hmargin.trans hzero) (hmargin.trans hone)

theorem case1_Y_closed_bracket_deriv_abs_lt (m : ℤ)
    (hm : m ∈ barrierCase1YBrackets) {x : ℝ}
    (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    |deriv barrierCase1Y x| < 102001 := by
  obtain ⟨hdom, hzero, hone⟩ := Case1Height.Y_closed_bracket_margins m hm hx
  have hmargin : (7 / 10000 : ℝ) ≤ 1 / 100 := by norm_num
  exact case1_Y_deriv_abs_lt hdom (hmargin.trans hzero) (hmargin.trans hone)

theorem case2_X_closed_bracket_deriv_abs_lt (m : ℤ)
    (hm : m ∈ barrierCase2XBrackets) {x : ℝ}
    (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    |deriv barrierCase2X x| < 12852 := by
  obtain ⟨hdom, _, hzero, hone⟩ := Case2Height.X_closed_bracket_margins m hm hx
  exact actual_X_deriv_abs_lt hdom hzero hone

theorem case2_Y_closed_bracket_deriv_abs_lt (m : ℤ)
    (hm : m ∈ barrierCase2YBrackets) {x : ℝ}
    (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    |deriv barrierCase2Y x| < 102001 := by
  obtain ⟨hdom, _, hzero, hone⟩ := Case2Height.Y_closed_bracket_margins m hm hx
  exact actual_Y_deriv_abs_lt hdom hzero hone

end InternalCatalan.ManuscriptSharpHeight

end

end

end OAI
