import OAI.NumberTheory.Ostmann.ZeroDensity.ZetaLocalLogDerivative
import OAI.NumberTheory.Ostmann.ZeroDensity.ShiftedRealHadamard

namespace OAI

/-! # The zeta-pole upper bound with logarithmic dependence on height -/

namespace Ostmann

open Complex

theorem regularizedZeta_logDeriv_lower (s : ℂ) (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    -(logDeriv regularizedZeta s).re ≤
      48 * (Real.log (96 * (|s.im| + 2) ^ 2) +
        (Real.log (96 * (|s.im| + 2) ^ 2) / Real.log (7 / 6)) * Real.log 6 + 1) := by
  have hh := zetaAtHeight_logDeriv_lower s.im s.re hs hs2
  have hcomp : logDeriv (zetaAtHeight s.im) ((s.re - 2 : ℝ) : ℂ) =
      logDeriv regularizedZeta s := by
    change logDeriv (regularizedZeta ∘ (fun z : ℂ => z + characterZeroCenter s.im)) _ = _
    rw [logDeriv_comp (g := fun z : ℂ => z + characterZeroCenter s.im)
      (regularizedZeta_analytic _).differentiableAt
      (differentiableAt_id.add_const _)]
    have he : ((s.re - 2 : ℝ) : ℂ) + characterZeroCenter s.im = s := by
      apply Complex.ext <;> simp [characterZeroCenter]
    convert congrArg (logDeriv regularizedZeta) he using 1
    simp
  rwa [hcomp] at hh

theorem exists_regularizedZeta_log_bound : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
      -(logDeriv regularizedZeta s).re ≤ C * Real.log (|s.im| + 2) := by
  let D := 1 + Real.log 6 / Real.log (7 / 6 : ℝ)
  let E := Real.log 96 / Real.log 2 + 2
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
  have h76 : 0 < Real.log (7 / 6 : ℝ) := Real.log_pos (by norm_num)
  have h96 : 0 < Real.log (96 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨48 * (D * E + 1 / Real.log 2), by positivity, ?_⟩
  intro s hs hs2
  let L := Real.log (|s.im| + 2)
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num)
    (show (2 : ℝ) ≤ |s.im| + 2 by linarith [abs_nonneg s.im])
  have hone : 1 ≤ (1 / Real.log 2) * L := by
    rw [one_div, inv_mul_eq_div]
    exact (le_div_iff₀ h2).mpr (by simpa using hL)
  have hconst : Real.log 96 ≤ (Real.log 96 / Real.log 2) * L := by
    have hh := mul_le_mul_of_nonneg_left hone h96.le
    convert hh using 1 <;> ring
  have hlog : Real.log (96 * (|s.im| + 2) ^ 2) = Real.log 96 + 2 * L := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    rfl
  have he : Real.log (96 * (|s.im| + 2) ^ 2) ≤ E * L := by
    rw [hlog]
    dsimp [E]
    nlinarith
  have hh := regularizedZeta_logDeriv_lower s hs hs2
  have hm := mul_le_mul_of_nonneg_left he hD.le
  have hform : Real.log (96 * (|s.im| + 2) ^ 2) +
      (Real.log (96 * (|s.im| + 2) ^ 2) / Real.log (7 / 6)) * Real.log 6 =
        D * Real.log (96 * (|s.im| + 2) ^ 2) := by dsimp [D]; ring
  rw [hform] at hh
  change _ ≤ 48 * (D * E + 1 / Real.log 2) * L
  nlinarith

/-- Uniform zeta-pole estimate, without any zero-free-region assumption. -/
theorem exists_vonMangoldt_logarithmic_upper : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re ≤
        realZeroKernel (s.re - 1) s.im + C * Real.log (|s.im| + 2) := by
  obtain ⟨C, hC, hb⟩ := exists_regularizedZeta_log_bound
  refine ⟨C, hC, ?_⟩
  intro s hs hs2
  have hh := hb s hs hs2
  rw [regularizedZeta_logDeriv s hs, Complex.add_re] at hh
  have he := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  change LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s = _ at he
  rw [he, neg_div, Complex.neg_re]
  have hk : ((s - 1)⁻¹).re = realZeroKernel (s.re - 1) s.im := by
    simpa using realZeroKernel_complex_sub s 1
  rw [hk] at hh
  simp only [logDeriv_apply] at hh
  linarith

end Ostmann

end OAI
