import OAI.NumberTheory.DirichletL.ContinuationContour
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
namespace SevenEighths.Continuation

def polynomialGaussian (n : ℕ) (y : ℝ) : ℝ :=
  (1+|y|^n)*Real.exp (-(y^2))

theorem polynomialGaussian_nonneg (n : ℕ) (y : ℝ) : 0 ≤ polynomialGaussian n y := by
  unfold polynomialGaussian
  positivity

theorem polynomialGaussian_even (n : ℕ) (y : ℝ) :
    polynomialGaussian n (-y) = polynomialGaussian n y := by
  simp [polynomialGaussian]

theorem polynomialGaussian_integrable (n : ℕ) : Integrable (polynomialGaussian n) := by
  have hp := (integrable_rpow_mul_exp_neg_mul_sq
    (by norm_num : (0 : ℝ)<1) (show (-1 : ℝ)<(n : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])).norm
  have hg := integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have he : (fun y : ℝ => ‖y^(n : ℝ)*Real.exp (-1*y^2)‖) =
      fun y : ℝ => |y|^n*Real.exp (-(y^2)) := by
    funext y
    simp [Real.rpow_natCast, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [he] at hp
  convert hg.add hp using 1
  funext y
  simp [polynomialGaussian, add_mul]

theorem polynomialGaussian_tendsto (n : ℕ) :
    Tendsto (polynomialGaussian n) atTop (𝓝 0) := by
  have hp := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (by norm_num : (0 : ℝ)<1) (n : ℝ)
  rw [cocompact_eq_atBot_atTop] at hp
  have hp' := hp.mono_left le_sup_right
  have hg : Tendsto (fun y : ℝ => Real.exp (-(y^2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by decide)))
  change Tendsto (fun y : ℝ => (1+|y|^n)*Real.exp (-(y^2))) atTop (𝓝 0)
  simpa [Real.rpow_natCast, add_mul] using hg.add hp'

theorem vertical_integral_eq_of_even_envelope (F : ℂ → ℂ) {a b C : ℝ}
    (E : ℝ → ℝ) (hE : Integrable E) (heven : ∀ y, E (-y)=E y)
    (hlim : Tendsto E atTop (𝓝 0)) (hab : a ≤ b)
    (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ, ‖F ((x : ℂ)+y*I)‖ ≤ C*E y) :
    (∫ y : ℝ, F ((a : ℂ)+y*I)) = ∫ y : ℝ, F ((b : ℂ)+y*I) := by
  have hc (x : ℝ) (hx : x ∈ Icc a b) : Continuous (fun y : ℝ => F ((x : ℂ)+y*I)) :=
    hhol.continuousOn.comp_continuous (by fun_prop) (by intro y; simpa using hx)
  have hint (x : ℝ) (hx : x ∈ Icc a b) : Integrable (fun y : ℝ => F ((x : ℂ)+y*I)) :=
    (hE.const_mul C).mono' (hc x hx).aestronglyMeasurable (ae_of_all _ (hbound x hx))
  have hhorizontal (sgn : ℝ) (heq : ∀ y, E (sgn*y)=E y) :
      Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ)+(sgn*T)*I)) atTop (𝓝 0) := by
    have hnorm (T : ℝ) : ‖∫ x : ℝ in a..b, F ((x : ℂ)+(sgn*T)*I)‖ ≤ C*E T*|b-a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      simpa only [heq, Complex.ofReal_mul] using hbound x (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx) (sgn*T)
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hnorm
      (by simpa using (hlim.const_mul C).mul_const |b-a|)
  apply vertical_integral_eq_of_horizontal_vanish F hab hhol
    (hint a ⟨le_rfl,hab⟩) (hint b ⟨hab,le_rfl⟩)
  · simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul] using hhorizontal (-1) (by simpa only [neg_one_mul] using heven)
  · simpa only [Complex.ofReal_one, one_mul] using hhorizontal 1 (by simp)

theorem vertical_integral_eq_of_polynomial_gaussian_bound (F : ℂ → ℂ)
    {a b C : ℝ} (n : ℕ) (hab : a ≤ b)
    (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ,
      ‖F ((x : ℂ)+y*I)‖ ≤ C*polynomialGaussian n y) :
    (∫ y : ℝ, F ((a : ℂ)+y*I)) = ∫ y : ℝ, F ((b : ℂ)+y*I) :=
  vertical_integral_eq_of_even_envelope F _ (polynomialGaussian_integrable n)
    (polynomialGaussian_even n) (polynomialGaussian_tendsto n) hab hhol hbound

end SevenEighths.Continuation

end

end OAI
