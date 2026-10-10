import OAI.NumberTheory.DirichletL.Detector.Row
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem fullIdealWeight_norm_eq_of_re (s t : ℂ) (h : s.re = t.re) (I : Ideal O) :
    ‖fullIdealWeight s I‖ = ‖fullIdealWeight t I‖ := by
  by_cases hI : I = 0
  · simp [hI, fullIdealWeight]
  · exact (norm_fullIdealWeight s ⟨I, hI⟩).trans
      ((by rw [h] : _ = _).trans (norm_fullIdealWeight t ⟨I, hI⟩).symm)

theorem fullIdealWeight_continuous (I : Ideal O) : Continuous (fun t => fullIdealWeight t I) := by
  by_cases hI : I = 0
  · simp only [hI, fullIdealWeight]
    exact continuous_const
  · have hn : (Ideal.absNorm I : ℂ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_ne_zero_iff I).mpr
        (Ring.HasFiniteQuotients.finiteQuotient hI)
    simp only [fullIdealWeight, ite_eq_right hI]
    exact continuous_id.neg.const_cpow (Or.inl hn)

def rowMajorant (σ : ℝ) (p : Ideal O × Ideal O) : ℝ :=
  2 * (‖fullIdealWeight (σ : ℂ) p.1‖ * ‖fullIdealWeight (3 * (σ : ℂ)) p.2‖)

theorem rowMajorant_summable (σ : ℝ) (hσ : 1 < σ) : Summable (rowMajorant σ) := by
  have h3 : 1 < (3 * (σ : ℂ)).re := by norm_num; linarith
  exact ((fullIdealWeight_summable_norm (σ : ℂ) hσ).mul_of_nonneg
    (fullIdealWeight_summable_norm (3 * (σ : ℂ)) h3)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left 2

theorem spectralSummand_vertical_bound (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ y : ℝ) (p : Ideal O × Ideal O) :
    ‖spectralSummand S D Ψ ((σ : ℂ) + y * Complex.I) p.1 p.2‖ ≤ rowMajorant σ p := by
  have h1 : ((σ : ℂ) + y * Complex.I).re = (σ : ℂ).re := by simp
  have h3 : (3 * ((σ : ℂ) + y * Complex.I)).re = (3 * (σ : ℂ)).re := by simp
  simpa only [rowMajorant, fullIdealWeight_norm_eq_of_re _ _ h1,
    fullIdealWeight_norm_eq_of_re _ _ h3] using
    spectralSummand_norm_le S D Ψ hΨ ((σ : ℂ) + y * Complex.I) p.1 p.2

theorem spectralRow_continuous_vertical (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ) :
    Continuous (fun y : ℝ => spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) := by
  apply continuous_tsum _ (rowMajorant_summable σ hσ)
    (fun p y => spectralSummand_vertical_bound S D Ψ hΨ σ y p)
  intro p
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  exact continuous_const.mul ((fullIdealWeight_continuous p.1).comp hc |>.mul
    ((fullIdealWeight_continuous p.2).comp (continuous_const.mul hc)))

theorem spectralRow_vertical_bound (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ) (y : ℝ) :
    ‖spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)‖ ≤ ∑' p, rowMajorant σ p := by
  have hs := spectralRow_summable S D Ψ hΨ ((σ : ℂ) + y * Complex.I) (by simpa using hσ)
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    (hs.norm.tsum_le_tsum (fun p => spectralSummand_vertical_bound S D Ψ hΨ σ y p)
      (rowMajorant_summable σ hσ))

theorem verticalKernel_norm (Z : ℝ) (hZ : 0 < Z) (σ y : ℝ) :
    ‖(Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2)‖ =
      Z ^ σ * Real.exp (σ ^ 2) * Real.exp (-1 * y ^ 2) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_exp]
  have hre : (((σ : ℂ) + y * Complex.I) ^ 2).re = σ ^ 2 + (-1 * y ^ 2) := by
    simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [hre, Real.exp_add]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  ring

theorem spectralRow_vertical_integrable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun y : ℝ => (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
      spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) := by
  let B : ℝ := ∑' p, rowMajorant σ p
  have hg := (integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul
    (Z ^ σ * Real.exp (σ ^ 2) * B)
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  have hk := (hc.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).mul ((hc.pow 2).cexp)
  apply hg.mono' (hk.mul (spectralRow_continuous_vertical S D Ψ hΨ σ hσ)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  dsimp only [Pi.mul_apply, Pi.pow_apply]
  rw [norm_mul, verticalKernel_norm Z hZ σ y]
  calc
    _ ≤ (Z ^ σ * Real.exp (σ ^ 2) * Real.exp (-1 * y ^ 2)) * B :=
      mul_le_mul_of_nonneg_left (spectralRow_vertical_bound S D Ψ hΨ σ hσ y)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.exp_pos _).le) (Real.exp_pos _).le)
    _ = _ := by ring

end SevenEighths.ProbeRow
end

end OAI
