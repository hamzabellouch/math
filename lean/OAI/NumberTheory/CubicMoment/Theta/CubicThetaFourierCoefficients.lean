import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFrequencyDirichlet

namespace OAI

/-! Fourier expansion with each arithmetic Dirichlet coefficient
collected, justified by absolute convergence of the full double sum. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicTheta_row_power {v : ℝ} (hv : 0<v) {c : Eisenstein} (hc : c≠0) (s : ℂ) :
    ((v/norm c:ℝ):ℂ)^s=(v:ℂ)^s*(norm c:ℂ)^(-s) := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hv.le
    (norm_pos_of_ne_zero hc).le,div_eq_mul_inv,Complex.cpow_neg]

theorem cubicThetaEisenstein_fourier_coefficients {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Complex.Gamma s*cubicThetaEisenstein p s=Complex.Gamma s*(p.2:ℂ)^s+
      (2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s*
        ∑' h : Eisenstein, cubicThetaFrequencyDirichlet h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  let F (c h : Eisenstein) := cubicThetaFrequencyTerm s h c*
    (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)
  have hF : Summable (fun ch : Eisenstein × Eisenstein => F ch.1 ch.2) :=
    (cubicThetaFrequency_heat_norm_summable hp hs).of_norm
  have hswap : (∑' c,∑' h, F c h)=(∑' h,∑' c, F c h) := hF.tsum_comm.symm
  calc
    _ = Complex.Gamma s*(p.2:ℂ)^s+
        ∑' c : Eisenstein, if (3:Eisenstein)∣c ∧ c≠0 then
          ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
            ∑' h : Eisenstein, cubicThetaRowFourierCoefficient c p.1 h*
              (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)
        else 0 := cubicThetaEisenstein_fourier_rows hp hs
    _ = Complex.Gamma s*(p.2:ℂ)^s+
        ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s)*(∑' c,∑' h, F c h) := by
      congr 1
      rw [←tsum_mul_left]
      apply tsum_congr
      intro c
      by_cases hc : (3:Eisenstein)∣c ∧ c≠0
      · rw [ite_eq_left hc,cubicTheta_row_power hp hc.2,←tsum_mul_left,←tsum_mul_left]
        apply tsum_congr
        intro h
        simp only [F,cubicThetaFrequencyTerm,ite_eq_left hc,cubicThetaRowFourierCoefficient]
        ring
      · simp [F,cubicThetaFrequencyTerm,hc]
    _ = Complex.Gamma s*(p.2:ℂ)^s+
        ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s)*(∑' h,∑' c, F c h) := by
      rw [hswap]
    _ = _ := by
      congr 2
      apply tsum_congr
      intro h
      dsimp only [F]
      rw [tsum_mul_right,tsum_mul_right]
      rfl

theorem cubicThetaEisenstein_fourier_normalized {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    cubicThetaEisenstein p s=(p.2:ℂ)^s+
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s/Complex.Gamma s)*
        ∑' h : Eisenstein, cubicThetaFrequencyDirichlet h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  have hG := Complex.Gamma_ne_zero_of_re_pos (show 0<s.re by linarith)
  apply (mul_left_cancel₀ hG)
  rw [cubicThetaEisenstein_fourier_coefficients hp hs,mul_add]
  field_simp

end CubicFirstMoment

end

end OAI
