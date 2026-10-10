import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedRowFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaZeroFourier

namespace OAI

/-! The full actual inverted Eisenstein series and its zero-frequency
row term. The scalar continuation retains the exact archimedean factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisenstein_inverted_fourier_rows {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Complex.Gamma s*cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      ∑' c : Eisenstein, if primary c then
        ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
          ∑' h : Eisenstein, cubicThetaInvertedRowFourierCoefficient c p.1 h*
            (∫ t in Set.Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)
        else 0 := by
  rw [cubicThetaEisenstein_inverted_rows hp hs,←tsum_mul_left]
  apply tsum_congr
  intro c
  by_cases hc : primary c
  · simpa only [ite_eq_left hc] using cubicThetaInvertedRow_fourier hc hp hs
  · simp only [ite_eq_right hc,mul_zero]

lemma cubicThetaInverted_zero_row_factor {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 1<s.re)
    {c : Eisenstein} (hc : primary c) :
    (((v/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
      cubicThetaInvertedGaussCoefficient c 0*
        (∫ t in Set.Ioi (0:ℝ), cubicThetaDualHeat v s 0 t))/Complex.Gamma s=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s)*
        (cubicThetaInvertedConstantGauss c*(norm c:ℂ)^(-s)) := by
  have hs0 : s-1≠0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.one_re,Complex.zero_re] at he
    linarith
  have hg := Complex.Gamma_add_one (s-1) hs0
  rw [sub_add_cancel] at hg
  rw [cubicThetaDualHeat_zero_integral hv hs,hg,cubicThetaInvertedGaussCoefficient_zero]
  have hp := cubicTheta_zero_height_factor hv (norm_pos_of_ne_zero (primary_ne_zero hc)) s
  have hG := Complex.Gamma_ne_zero_of_re_pos
    (show 0<(s-1).re by simp only [Complex.sub_re,Complex.one_re]; linarith)
  calc
    _ = ((v/norm c:ℝ):ℂ)^s*((v^2:ℝ):ℂ)^(1-s)*
        (2*Real.pi/(9*Real.sqrt 3):ℂ)*cubicThetaInvertedConstantGauss c/(s-1) := by
      field_simp
    _ = _ := by rw [hp]; ring

def cubicThetaInvertedConstantMode (v : ℝ) (s : ℂ) : ℂ :=
  ∑' c : Eisenstein, if primary c then
    (((v/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
      cubicThetaInvertedGaussCoefficient c 0*
        (∫ t in Set.Ioi (0:ℝ), cubicThetaDualHeat v s 0 t))/Complex.Gamma s else 0

theorem cubicThetaInvertedConstantMode_eq {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 1<s.re) :
    cubicThetaInvertedConstantMode v s=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s)*cubicThetaInvertedConstantDirichlet s := by
  unfold cubicThetaInvertedConstantMode cubicThetaInvertedConstantDirichlet
  rw [←tsum_mul_left]
  apply tsum_congr
  intro c
  by_cases hc : primary c
  · simp only [cubicThetaInvertedConstantWeight,ite_eq_left hc]
    exact cubicThetaInverted_zero_row_factor hv hs hc
  · simp [hc,cubicThetaInvertedConstantWeight]

def cubicThetaInvertedModeContinuation (v : ℝ) (s : ℂ) : ℂ :=
  ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s)*cubicThetaInvertedConstantContinuation s

theorem cubicThetaInvertedModeContinuation_right {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 4/3<s.re) :
    cubicThetaInvertedConstantMode v s=cubicThetaInvertedModeContinuation v s := by
  rw [cubicThetaInvertedConstantMode_eq hv (by linarith),cubicThetaInvertedConstantContinuation_right hs]
  rfl

end CubicFirstMoment

end

end OAI
