import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeNormRange

namespace OAI

/-! Exact Mellin separation on the literal full prime-convolution support.
The compact log-norm range follows from the coordinate supports. -/
noncomputable section
open scoped BigOperators ContDiff
open Set MeasureTheory
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeConvolutionLogRadius (R : ℝ) (n : ℕ) : ℝ := 1+2*Real.log (R^n)

lemma primeConvolutionLogRadius_pos {R : ℝ} (hR : 1 ≤ R) (n : ℕ) :
    0 < primeConvolutionLogRadius R n := by
  have h := Real.log_nonneg (one_le_pow₀ hR : (1:ℝ) ≤ R^n)
  dsimp [primeConvolutionLogRadius]
  linarith

lemma fullPrimeMellin_log_range {R J : ℝ} (hR : 1 ≤ R) (hJ : 0 < J)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (e : Eisenstein) (H : Finset Eisenstein) (hH : ∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) :
    ∀ h ∈ H, ∀ a ∈ fullSquarefreePrimeSupport R W X e,
      ∀ b ∈ fullSquarefreePrimeSupport R W X e,
      |Real.log (norm h/J)-Real.log ((norm a/(∏ i, X i))*(norm b/(∏ i, X i)))| ≤
        primeConvolutionLogRadius R (Fintype.card ι) := by
  intro h hh a ha b hb
  apply compact_norm_log_ratio (one_le_pow₀ hR)
    (y := norm a/(∏ i, X i)) (z := norm b/(∏ i, X i))
  · exact ⟨(le_div_iff₀ hJ).mpr (by simpa only [one_mul] using (hH h hh).1),
      (div_le_iff₀ hJ).mpr (hH h hh).2⟩
  · exact fullSquarefreePrimeSupport_scaled_norm R W X hX hlo hhi e ha
  · exact fullSquarefreePrimeSupport_scaled_norm R W X hX hlo hhi e hb

theorem fullPrime_coprime_radial_mellin {R J : ℝ} (hR : 1 ≤ R) (hJ : 0 < J)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (e : Eisenstein) (H : Finset Eisenstein) (hH : ∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J)
    (v w phase : Eisenstein → ℂ) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    coprimeRadialForm (fullSquarefreePrimeSupport R W X e) H v w phase
      (fun h => norm h/J) (fun b => norm b/(∏ i, X i)) V ρ =
      ∫ t : ℝ, wideGramMellinCoefficient (primeConvolutionLogRadius R (Fintype.card ι))
        (primeConvolutionLogRadius_pos hR _) V hV hV' ρ t *
        coprimeMellinKernel (fullSquarefreePrimeSupport R W X e) H v w phase
          (fun h => norm h/J) (fun b => norm b/(∏ i, X i)) t := by
  apply wideCoprimeRadialForm_mellin
  · intro h hh
    exact div_pos (hJ.trans_le (hH h hh).1) hJ
  · intro b hb
    exact zero_lt_one.trans_le (fullSquarefreePrimeSupport_scaled_norm R W X hX hlo hhi e hb).1
  · exact fullPrimeMellin_log_range hR hJ W X hX hlo hhi e H hH
  · exact hρ

end CubicFirstMoment

end

end OAI
