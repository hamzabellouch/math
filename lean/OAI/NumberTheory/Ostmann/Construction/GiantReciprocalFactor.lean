import OAI.NumberTheory.Ostmann.Characters.LogCutoffPolynomial
import OAI.NumberTheory.Ostmann.Characters.ReciprocalPolynomialFactor

namespace OAI

/-! # The normalized reciprocal giant factor in the diagonal multiplier -/

namespace Ostmann

/-- Reuse the existing reciprocal factor after scaling the polynomial by
its lower cell endpoint. The variation budget is independent of the center. -/
noncomputable def giantReciprocalFactor (P : Polynomial ℝ) (G : ℝ) : ClippedPolynomialFactor :=
  reciprocalPolynomialFactor (Polynomial.C ((Real.exp (G - 1))⁻¹) * P) (Real.exp 2)
    (Real.one_le_exp (by norm_num))

theorem giantReciprocalFactor_budget (P : Polynomial ℝ) (G : ℝ) :
    2 * (giantReciprocalFactor P G).bound + (giantReciprocalFactor P G).lip *
      ((giantReciprocalFactor P G).hi - (giantReciprocalFactor P G).lo) = 1 + Real.exp 2 := by
  rw [giantReciprocalFactor, reciprocalPolynomialFactor_budget, add_comm]

theorem giantReciprocalFactor_value (P : Polynomial ℝ) (G x : ℝ)
    (hx : P.eval x ∈ Set.Icc (Real.exp (G - 1)) (Real.exp (G + 1))) :
    (Real.exp 1 : ℂ) * (giantReciprocalFactor P G).value x = (Real.exp G / P.eval x : ℝ) := by
  have hlo : 0 < Real.exp (G - 1) := Real.exp_pos _
  have hp : 0 < P.eval x := hlo.trans_le hx.1
  have hrange : P.eval x / Real.exp (G - 1) ∈ Set.Icc (1 : ℝ) (Real.exp 2) := by
    refine ⟨(one_le_div hlo).mpr hx.1, ?_⟩
    calc
      _ ≤ Real.exp (G + 1) / Real.exp (G - 1) := div_le_div_of_nonneg_right hx.2 hlo.le
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  rw [giantReciprocalFactor, reciprocalPolynomialFactor_original _ _ _ x
    (Real.exp (G - 1)) (P.eval x) hlo.ne' hp.ne'
    (by simp only [Polynomial.eval_mul, Polynomial.eval_C, div_eq_mul_inv, mul_comm]) hrange,
    ← Complex.ofReal_mul]
  apply congrArg (fun a : ℝ => (a : ℂ))
  rw [← mul_div_assoc, ← Real.exp_add, show 1 + (G - 1) = G by ring]

/-- Multiplication by the actual giant cutoff makes the clipped reciprocal
identical to the manuscript's reciprocal everywhere, including zero terms. -/
theorem giantReciprocalFactor_cutoff (P : Polynomial ℝ) (φ : ℝ → ℝ)
    (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (x : ℝ) :
    (logCutoffPolynomialFactor P φ G B D hB hD hφ hlip).value x *
      ((Real.exp 1 : ℂ) * (giantReciprocalFactor P G).value x) =
        (positiveLogCutoff φ G (P.eval x) : ℂ) * (Real.exp G / P.eval x : ℝ) := by
  rw [logCutoffPolynomialFactor_value P φ G B D hB hD hφ hlip hout x]
  by_cases hz : positiveLogCutoff φ G (P.eval x) = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  · have hx : 0 < P.eval x := by
      by_contra hn
      exact hz (by simp only [positiveLogCutoff, ite_eq_right hn])
    have hn : φ (Real.log (P.eval x) - G) ≠ 0 := by
      simpa only [positiveLogCutoff, ite_eq_left hx] using hz
    have hr : |Real.log (P.eval x) - G| < 1 := lt_of_not_ge (fun h => hn (hout _ h))
    have hbounds : P.eval x ∈ Set.Icc (Real.exp (G - 1)) (Real.exp (G + 1)) := by
      have h := abs_lt.mp hr
      constructor
      · rw [← Real.exp_log hx]
        exact Real.exp_le_exp.mpr (by linarith)
      · rw [← Real.exp_log hx]
        exact Real.exp_le_exp.mpr (by linarith)
    rw [giantReciprocalFactor_value P G x hbounds]

end Ostmann

end OAI
