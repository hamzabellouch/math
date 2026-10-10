import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

namespace OAI

/-! An explicit comparison function for the lower-volume sine remainder. -/
namespace PositiveEinsteinFour.Jacobi
noncomputable section

def sineLogPolynomial (x : ℝ) : ℝ := x ^ 2 / 6 + x ^ 4 / 180 + x ^ 6 / 2835
def sineCotPolynomial (x : ℝ) : ℝ := 1 - x ^ 2 / 3 - x ^ 4 / 45 - 2 * x ^ 6 / 945
def sineLogRate (x : ℝ) : ℝ := x / 3 + x ^ 3 / 45 + 2 * x ^ 5 / 945
def sineLogResidual (x : ℝ) : ℝ := x ^ 7 / 525 + 4 * x ^ 9 / 42525 + 4 * x ^ 11 / 893025
def sineLogWronskian (x : ℝ) : ℝ :=
  Real.exp (-sineLogPolynomial x) * (sineCotPolynomial x * Real.sin x - x * Real.cos x)

theorem sineLogPolynomial_hasDerivAt (x : ℝ) :
    HasDerivAt sineLogPolynomial (sineLogRate x) x := by
  convert (((hasDerivAt_id x).pow 2).div_const 6 |>.add
    (((hasDerivAt_id x).pow 4).div_const 180)).add
    (((hasDerivAt_id x).pow 6).div_const 2835) using 1
  all_goals first | rfl | (dsimp [sineLogRate]; ring)

theorem sineCotPolynomial_hasDerivAt (x : ℝ) :
    HasDerivAt sineCotPolynomial (-2 * x / 3 - 4 * x ^ 3 / 45 - 12 * x ^ 5 / 945) x := by
  convert (((hasDerivAt_const x (1 : ℝ)).sub
    (((hasDerivAt_id x).pow 2).div_const 3)).sub
    (((hasDerivAt_id x).pow 4).div_const 45)).sub
    ((((hasDerivAt_id x).pow 6).const_mul 2).div_const 945) using 1
  all_goals first | rfl | (dsimp; ring)

theorem sineLogWronskian_hasDerivAt (x : ℝ) :
    HasDerivAt sineLogWronskian
      (Real.exp (-sineLogPolynomial x) * sineLogResidual x * Real.sin x) x := by
  have he := ((sineLogPolynomial_hasDerivAt x).neg).exp
  have hw := ((sineCotPolynomial_hasDerivAt x).mul (Real.hasDerivAt_sin x)).sub
    ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))
  convert he.mul hw using 1
  · rfl
  · dsimp [sineCotPolynomial, sineLogRate, sineLogResidual]
    ring

theorem sineLogWronskian_nonneg {x : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    0 ≤ sineLogWronskian x := by
  have hm : MonotoneOn sineLogWronskian (Set.Icc 0 Real.pi) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    · exact (continuous_iff_continuousAt.mpr
        (fun s => (sineLogWronskian_hasDerivAt s).continuousAt)).continuousOn
    · intro s hs
      exact (sineLogWronskian_hasDerivAt s).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs0 : 0 ≤ s := hs.1.le
      have hr : 0 ≤ sineLogResidual s := by unfold sineLogResidual; positivity
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hr)
        (Real.sin_nonneg_of_nonneg_of_le_pi hs.1.le hs.2.le)
  have h := hm (by simp [Real.pi_pos.le]) ⟨hx,hxπ⟩ hx
  simpa [sineLogWronskian, sineLogPolynomial, sineCotPolynomial] using h

end
end PositiveEinsteinFour.Jacobi

end OAI
