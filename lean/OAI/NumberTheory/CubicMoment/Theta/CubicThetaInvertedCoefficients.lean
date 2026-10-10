import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedFrequencyBounds

namespace OAI

/-! Collect the inverted Fourier coefficients by an absolutely
convergent interchange of the two actual lattice sums. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisenstein_inverted_fourier_coefficients {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Complex.Gamma s*cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      (2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s*
        ∑' h : Eisenstein, cubicThetaInvertedFrequencyDirichlet h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  let F (c h : Eisenstein) := cubicThetaInvertedFrequencyTerm s h c*
    (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)
  have hF : Summable (fun ch : Eisenstein × Eisenstein => F ch.1 ch.2) :=
    (cubicThetaInvertedFrequency_heat_norm_summable hp hs).of_norm
  have hswap : (∑' c,∑' h,F c h)=(∑' h,∑' c,F c h) := hF.tsum_comm.symm
  rw [cubicThetaEisenstein_inverted_fourier_rows hp hs]
  calc
    _ = ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s)*(∑' c,∑' h,F c h) := by
      rw [←tsum_mul_left]
      apply tsum_congr
      intro c
      by_cases hc : primary c
      · rw [ite_eq_left hc,cubicTheta_row_power hp (primary_ne_zero hc),
          ←tsum_mul_left,←tsum_mul_left]
        apply tsum_congr
        intro h
        simp only [F,cubicThetaInvertedFrequencyTerm,ite_eq_left hc,
          cubicThetaInvertedRowFourierCoefficient]
        ring
      · simp [F,cubicThetaInvertedFrequencyTerm,hc]
    _ = ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s)*(∑' h,∑' c,F c h) := by rw [hswap]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro h
      dsimp only [F]
      rw [tsum_mul_right,tsum_mul_right,cubicThetaInvertedFrequencyDirichlet_tsum]

theorem cubicThetaEisenstein_inverted_fourier_normalized {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s/Complex.Gamma s)*
        ∑' h : Eisenstein, cubicThetaInvertedFrequencyDirichlet h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  have hG := Complex.Gamma_ne_zero_of_re_pos (show 0<s.re by linarith)
  apply mul_left_cancel₀ hG
  rw [cubicThetaEisenstein_inverted_fourier_coefficients hp hs]
  field_simp

lemma cubicThetaInvertedFourierCoefficients_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Summable (fun h : Eisenstein => cubicThetaInvertedFrequencyDirichlet h s*
      (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)) := by
  have h := (cubicThetaInvertedFrequency_heat_norm_summable hp hs).of_norm.prod_symm.prod
  apply h.congr
  intro n
  dsimp only [Prod.swap]
  rw [tsum_mul_right,tsum_mul_right,cubicThetaInvertedFrequencyDirichlet_tsum]

def cubicThetaInvertedNonzeroTerm (p : ℂ × ℝ) (s : ℂ) (h : Eisenstein) : ℂ :=
  if h=0 then 0 else cubicThetaInvertedFrequencyDirichlet h s*
    (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)

lemma cubicThetaInvertedNonzeroTerm_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) : Summable (cubicThetaInvertedNonzeroTerm p s) := by
  apply (cubicThetaInvertedFourierCoefficients_summable hp hs).norm.of_norm_bounded
  intro h
  by_cases hh : h=0
  · simp only [cubicThetaInvertedNonzeroTerm,ite_eq_left hh,norm_zero]
    exact _root_.norm_nonneg _
  · simp only [cubicThetaInvertedNonzeroTerm,ite_eq_right hh,le_refl]

theorem cubicThetaEisenstein_inverted_nonzero {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      cubicThetaInvertedConstantMode p.2 s+
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s/Complex.Gamma s)*
        ∑' h : Eisenstein, cubicThetaInvertedNonzeroTerm p s h := by
  rw [cubicThetaEisenstein_inverted_fourier_normalized hp hs,
    (cubicThetaInvertedFourierCoefficients_summable hp hs).tsum_eq_add_tsum_ite 0,
    cubicThetaInvertedFrequencyDirichlet_zero,cubicThetaRowHeatScale_zero]
  have hphase : (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency 0)):ℂ)=1 := by
    simp [cubicThetaRowFrequency,tracePair]
  rw [hphase,mul_one,mul_add,cubicTheta_zero_mode_archimedean hp (show 1<s.re by linarith),
    cubicThetaInvertedConstantMode_eq hp (show 1<s.re by linarith)]
  rfl

end CubicFirstMoment

end

end OAI
