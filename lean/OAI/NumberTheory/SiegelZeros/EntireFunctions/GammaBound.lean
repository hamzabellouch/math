import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.Linarith

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W52

noncomputable def gammaLogDerivative (z : ℂ) : ℂ :=
  deriv Complex.Gamma z / Complex.Gamma z

theorem analyticAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.Gamma z := by
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := by
    intro w hw
    apply (Complex.differentiableAt_Gamma w ?_).differentiableWithinAt
    intro m hm
    have hr := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hr
    have hn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    change 0 < w.re at hw
    linarith
  exact hd.analyticAt (ho.mem_nhds hz)

theorem continuousAt_gammaLogDerivative {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt gammaLogDerivative z := by
  have ha := analyticAt_Gamma_of_re_pos hz
  exact ha.deriv.continuousAt.div ha.continuousAt (Complex.Gamma_ne_zero_of_re_pos hz)

theorem exists_gammaLogDerivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ) →
      ‖gammaLogDerivative (x : ℂ)‖ ≤ C := by
  have hc : ContinuousOn (fun x : ℝ => gammaLogDerivative (x : ℂ))
      (Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ)) := by
    intro x hx
    have hp : 0 < (x : ℂ).re := by
      simp only [Complex.ofReal_re]
      linarith [hx.1]
    exact ((continuousAt_gammaLogDerivative hp).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max B 0 + 1, by positivity, ?_⟩
  intro x hx
  exact (hB x hx).trans (le_trans (le_max_left B 0) (by linarith))

theorem exists_uniform_parity_gamma_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (ε : ℕ),
      1 < s → s ≤ 2 → (ε = 0 ∨ ε = 1) →
      ‖deriv Complex.Gamma (((s + (ε : ℝ)) / 2 : ℝ) : ℂ) /
        Complex.Gamma (((s + (ε : ℝ)) / 2 : ℝ) : ℂ)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_gammaLogDerivative_bound
  refine ⟨C, hC, ?_⟩
  intro s ε hs hs' hε
  apply hbound
  rcases hε with rfl | rfl <;> simp only [Nat.cast_zero, Nat.cast_one] <;>
    constructor <;> linarith

end SiegelZerosAwei.W52

end

end SiegelZeros

end OAI
