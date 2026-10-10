import OAI.Analysis.KadisonKastler.PeriodicStripExtension
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace OAI

/-! # The exponential determined by a scalar KMS balance equation -/

namespace KadisonKastler

open Complex

noncomputable section

/-- A positive modular frequency is uniquely determined by the ratio
of the boundary values of its bounded KMS strip. -/
theorem kms_strip_exponential {f : ℂ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1})
    (hd : DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1})
    (hb : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → ‖f z‖ ≤ C)
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = (Real.exp (-L) : ℂ) * f t) :
    ∀ t : ℝ, f t = Complex.exp (I * (L : ℂ) * t) * f 0 := by
  let g : ℂ → ℂ := fun z => Complex.exp (-I * (L : ℂ) * z) * f z
  have hge (t : ℝ) : g ((t : ℂ) + I) = g t := by
    dsimp [g]
    rw [he, ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    calc
      -I * (L : ℂ) * ((t : ℂ) + I) + -(L : ℂ) =
        -I * (L : ℂ) * t - (L : ℂ) * I ^ 2 - L := by ring
      _ = -I * (L : ℂ) * t := by rw [I_sq]; ring
  have hgc : ContinuousOn g {z | 0 ≤ z.im ∧ z.im ≤ 1} :=
    (by fun_prop : Continuous (fun z : ℂ => Complex.exp (-I * (L : ℂ) * z))).continuousOn.mul hc
  have hgd : DifferentiableOn ℂ g {z | 0 < z.im ∧ z.im < 1} :=
    (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (-I * (L : ℂ) * z))).differentiableOn.mul hd
  obtain ⟨C, hC⟩ := hb
  have hgb : ∃ B : ℝ, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → ‖g z‖ ≤ B := by
    refine ⟨Real.exp L * C, ?_⟩
    intro z hz₁ hz₂
    have hre : (-I * (L : ℂ) * z).re = L * z.im := by simp
    calc
      ‖g z‖ = Real.exp (L * z.im) * ‖f z‖ := by
        simp only [g, norm_mul, Complex.norm_exp, hre]
      _ ≤ Real.exp L * C := mul_le_mul
        (Real.exp_le_exp.mpr (mul_le_of_le_one_right hL hz₂)) (hC z hz₁ hz₂)
        (norm_nonneg _) (Real.exp_pos _).le
  intro t
  have hg := bounded_matching_strip_constant hge hgc hgd hgb (t : ℂ) (by simp) (by simp)
  have hinv : Complex.exp (I * (L : ℂ) * t) * Complex.exp (-I * (L : ℂ) * t) = 1 := by
    rw [← Complex.exp_add]
    rw [show I * (L : ℂ) * t + -I * (L : ℂ) * t = 0 by ring, Complex.exp_zero]
  have h := congrArg (fun w : ℂ => Complex.exp (I * (L : ℂ) * t) * w) hg
  simpa only [g, ← mul_assoc, hinv, one_mul, mul_zero, Complex.exp_zero, mul_one] using h

end

end KadisonKastler

end OAI
