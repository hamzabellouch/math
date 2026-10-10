import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierCoefficients

namespace OAI

/-! The centered Eisenstein expansion on the original half-plane,
with the continued constant coefficient separated from the actual
nonzero arithmetic Fourier coefficients. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaFourierCoefficients_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Summable (fun h : Eisenstein => cubicThetaFrequencyDirichlet h s*
      (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)) := by
  have h := (cubicThetaFrequency_heat_norm_summable hp hs).of_norm.prod_symm.prod
  apply h.congr
  intro n
  dsimp only [Prod.swap]
  rw [tsum_mul_right,tsum_mul_right]
  rfl

lemma cubicTheta_zero_mode_archimedean {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 1<s.re)
    (D : ℂ) :
    ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
      (D*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s 0 t))=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s)*D := by
  have hs0 : s-1≠0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.one_re,Complex.zero_re] at he
    linarith
  have hg := Complex.Gamma_add_one (s-1) hs0
  rw [sub_add_cancel] at hg
  have hG := Complex.Gamma_ne_zero_of_re_pos
    (show 0<(s-1).re by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have hf := cubicTheta_zero_height_factor hv (by norm_num : (0:ℝ)<1) s
  simp only [div_one,Complex.ofReal_one,Complex.one_cpow,mul_one] at hf
  rw [cubicThetaDualHeat_zero_integral hv hs,hg]
  calc
    _ = ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*
        ((v:ℂ)^s*((v^2:ℝ):ℂ)^(1-s))*D := by field_simp
    _ = _ := by rw [hf]

theorem cubicThetaEisenstein_nonzero_coefficients {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    cubicThetaEisenstein p s=cubicThetaEisensteinConstantMode p.2 s+
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s/Complex.Gamma s)*
        ∑' h : Eisenstein, if h=0 then 0 else cubicThetaFrequencyDirichlet h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  rw [cubicThetaEisenstein_fourier_normalized hp hs,
    (cubicThetaFourierCoefficients_summable hp hs).tsum_eq_add_tsum_ite 0,
    cubicThetaFrequencyDirichlet_zero,cubicThetaRowHeatScale_zero]
  have hphase : (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency 0)):ℂ)=1 := by
    simp [cubicThetaRowFrequency,tracePair]
  rw [hphase,mul_one,mul_add,cubicTheta_zero_mode_archimedean hp (show 1<s.re by linarith),
    cubicThetaEisensteinConstantMode_eq hp (show 1<s.re by linarith)]
  ring

theorem cubicThetaEisenstein_continued_constant_split {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    cubicThetaEisenstein p s=(p.2:ℂ)^s+
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(p.2:ℂ)^(2-s)*
        cubicThetaConstantContinuation s+
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s/Complex.Gamma s)*
        ∑' h : Eisenstein, if h=0 then 0 else cubicThetaFrequencyDirichlet h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  rw [cubicThetaEisenstein_nonzero_coefficients hp hs,
    cubicThetaEisensteinConstantMode_eq hp (show 1<s.re by linarith),
    cubicThetaConstantContinuation_right (show 4/3<s.re by linarith)]

end CubicFirstMoment

end

end OAI
