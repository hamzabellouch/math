import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinFourierRows
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantContinuation

namespace OAI

/-! The zero Fourier mode of the actual Eisenstein row expansion,
including its exact archimedean factor. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaDualHeat_zero_integral {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 1<s.re) :
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s 0 t)=
      Complex.Gamma (s-1)*((v^2:ℝ):ℂ)^(1-s) := by
  have hi := cubicThetaLaplaceTerm_integral (1:ℂ) (sq_pos_of_pos hv)
    (show 0<(s-1).re by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have he : (fun t => cubicThetaDualHeat v s 0 t)=cubicThetaLaplaceTerm 1 (v^2) (s-1) := by
    funext t
    simp only [cubicThetaDualHeat,cubicThetaLaplaceTerm,zero_div,sub_zero,one_mul]
    rw [show s-1-1=s-2 by ring]
  rw [he,hi]
  simp only [one_mul]
  rw [show -(s-1)=1-s by ring]

lemma cubicTheta_zero_height_factor {v n : ℝ} (hv : 0<v) (hn : 0<n) (s : ℂ) :
    ((v/n:ℝ):ℂ)^s*((v^2:ℝ):ℂ)^(1-s)=
      (v:ℂ)^(2-s)*(n:ℂ)^(-s) := by
  have hv0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hn0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have hp : ((v^2:ℝ):ℂ)^(1-s)=(v:ℂ)^(2*(1-s)) := by
    rw [Complex.ofReal_pow,←Complex.cpow_nat_mul' (n:=2)
      (by rw [Complex.arg_ofReal_of_nonneg hv.le]; nlinarith [Real.pi_pos])
      (by rw [Complex.arg_ofReal_of_nonneg hv.le]; nlinarith [Real.pi_pos])]
    norm_num
  rw [hp,Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hv.le hn.le,Complex.cpow_neg]
  calc
    _ = ((v:ℂ)^s*(v:ℂ)^(2*(1-s)))*((n:ℂ)^s)⁻¹ := by ring
    _ = _ := by
      rw [←Complex.cpow_add _ _ hv0]
      congr 2
      ring

lemma cubicTheta_zero_row_factor {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 1<s.re)
    {c : Eisenstein} (hc : c≠0) :
    (((v/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
      cubicThetaEisensteinGaussCoefficient c 0*
        (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s 0 t))/Complex.Gamma s =
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s)*
        (cubicThetaEisensteinGaussCoefficient c 0*(norm c:ℂ)^(-s)) := by
  have hs0 : s-1≠0 := by intro h; have he := congrArg Complex.re h; simp only [Complex.sub_re,Complex.one_re,Complex.zero_re] at he; linarith
  have hg := Complex.Gamma_add_one (s-1) hs0
  rw [sub_add_cancel] at hg
  rw [cubicThetaDualHeat_zero_integral hv hs,hg]
  have hp := cubicTheta_zero_height_factor hv (norm_pos_of_ne_zero hc) s
  have hG := Complex.Gamma_ne_zero_of_re_pos
    (show 0<(s-1).re by simp only [Complex.sub_re,Complex.one_re]; linarith)
  calc
    _ = ((v/norm c:ℝ):ℂ)^s*((v^2:ℝ):ℂ)^(1-s)*
        (2*Real.pi/(9*Real.sqrt 3):ℂ)*cubicThetaEisensteinGaussCoefficient c 0/(s-1) := by
      field_simp
    _ = _ := by rw [hp]; ring

def cubicThetaEisensteinConstantMode (v : ℝ) (s : ℂ) : ℂ :=
  (v:ℂ)^s+∑' c : Eisenstein, if (3:Eisenstein)∣c ∧ c≠0 then
    (((v/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
      cubicThetaEisensteinGaussCoefficient c 0*
        (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s 0 t))/Complex.Gamma s else 0

theorem cubicThetaEisensteinConstantMode_eq {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 1<s.re) :
    cubicThetaEisensteinConstantMode v s=(v:ℂ)^s+
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s)*cubicThetaConstantDirichlet s := by
  unfold cubicThetaEisensteinConstantMode cubicThetaConstantDirichlet
  rw [←tsum_mul_left]
  congr 1
  apply tsum_congr
  intro c
  by_cases hc : (3:Eisenstein)∣c ∧ c≠0
  · simp only [cubicThetaConstantTermWeight,ite_eq_left hc]
    exact cubicTheta_zero_row_factor hv hs hc.2
  · simp [hc,cubicThetaConstantTermWeight]

end CubicFirstMoment

end

end OAI
