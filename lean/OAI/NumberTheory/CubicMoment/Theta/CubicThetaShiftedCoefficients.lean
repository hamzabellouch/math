import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedFrequencyBounds

namespace OAI

/-! Collect the inverted Fourier coefficients by an absolutely
convergent interchange of the two actual lattice sums. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisenstein_shifted_fourier_rows (b : Eisenstein) {p : ℂ×ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Complex.Gamma s*cubicThetaEisenstein
      ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s=
      ∑' c : Eisenstein, if primary c then
        ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(81*Real.sqrt 3):ℂ)*
          ∑' h : Eisenstein, cubicThetaShiftedRowFourierCoefficient b c p.1 h*
            (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t)
        else 0 := by
  rw [cubicThetaEisenstein_shifted_rows b hp hs,←tsum_mul_left]
  apply tsum_congr
  intro c
  by_cases hc : primary c
  · simpa only [ite_eq_left hc] using cubicThetaShiftedRow_fourier b hc hp hs
  · simp only [ite_eq_right hc,mul_zero]

theorem cubicThetaEisenstein_shifted_fourier_coefficients (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Complex.Gamma s*cubicThetaEisenstein
      ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s=
      (2*Real.pi/(81*Real.sqrt 3):ℂ)*(p.2:ℂ)^s*
        ∑' h : Eisenstein, cubicThetaShiftedFrequencyDirichlet b h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t) := by
  let F (c h : Eisenstein) := cubicThetaShiftedFrequencyTerm b s h c*
    (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency h)):ℂ)*
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t)
  have hF : Summable (fun ch : Eisenstein × Eisenstein => F ch.1 ch.2) :=
    (cubicThetaShiftedFrequency_heat_norm_summable b hp hs).of_norm
  have hswap : (∑' c,∑' h,F c h)=(∑' h,∑' c,F c h) := hF.tsum_comm.symm
  rw [cubicThetaEisenstein_shifted_fourier_rows b hp hs]
  calc
    _ = ((2*Real.pi/(81*Real.sqrt 3):ℂ)*(p.2:ℂ)^s)*(∑' c,∑' h,F c h) := by
      rw [←tsum_mul_left]
      apply tsum_congr
      intro c
      by_cases hc : primary c
      · rw [ite_eq_left hc,cubicTheta_row_power hp (primary_ne_zero hc),
          ←tsum_mul_left,←tsum_mul_left]
        apply tsum_congr
        intro h
        simp only [F,cubicThetaShiftedFrequencyTerm,ite_eq_left hc,
          cubicThetaShiftedRowFourierCoefficient]
        ring
      · simp [F,cubicThetaShiftedFrequencyTerm,hc]
    _ = ((2*Real.pi/(81*Real.sqrt 3):ℂ)*(p.2:ℂ)^s)*(∑' h,∑' c,F c h) := by rw [hswap]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro h
      dsimp only [F]
      rw [tsum_mul_right,tsum_mul_right,cubicThetaShiftedFrequencyDirichlet_tsum]

theorem cubicThetaEisenstein_shifted_fourier_normalized (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    cubicThetaEisenstein
      ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s=
      ((2*Real.pi/(81*Real.sqrt 3):ℂ)*(p.2:ℂ)^s/Complex.Gamma s)*
        ∑' h : Eisenstein, cubicThetaShiftedFrequencyDirichlet b h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t) := by
  have hG := Complex.Gamma_ne_zero_of_re_pos (show 0<s.re by linarith)
  apply mul_left_cancel₀ hG
  rw [cubicThetaEisenstein_shifted_fourier_coefficients b hp hs]
  field_simp

lemma cubicThetaShiftedFourierCoefficients_summable (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Summable (fun h : Eisenstein => cubicThetaShiftedFrequencyDirichlet b h s*
      (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency h)):ℂ)*
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t)) := by
  have h := (cubicThetaShiftedFrequency_heat_norm_summable b hp hs).of_norm.prod_symm.prod
  apply h.congr
  intro n
  dsimp only [Prod.swap]
  rw [tsum_mul_right,tsum_mul_right,cubicThetaShiftedFrequencyDirichlet_tsum]

end CubicFirstMoment

end

end OAI
