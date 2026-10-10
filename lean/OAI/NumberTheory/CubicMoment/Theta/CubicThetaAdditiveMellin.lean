import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelMellin

namespace OAI

/-! Identify the initial Dirichlet series of each rationally shifted
theta function before using its continued Mellin expression. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaAdditiveCoefficient (z : ℂ) (n : Eisenstein) : ℂ :=
  cubicThetaArithmeticCoefficient n*
    (Real.fourierChar (tracePair (cubicThetaFrequency n) z):ℂ)

lemma cubicThetaAdditiveCoefficient_norm (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaAdditiveCoefficient z n‖≤81 := by
  simpa only [cubicThetaAdditiveCoefficient,norm_mul,Circle.norm_coe,mul_one] using
    cubicThetaArithmeticCoefficient_norm_le n

lemma cubicThetaAdditiveCoefficient_term (z : ℂ) (v : ℝ) (n : Eisenstein) :
    cubicThetaSeriesTerm (cubicThetaAdditiveCoefficient z) 0 v n=
      cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v n := by
  classical
  by_cases hn : n=0
  · simp only [cubicThetaSeriesTerm,hn,ite_true]
  · simp only [cubicThetaSeriesTerm,hn,ite_false,cubicThetaAdditiveCoefficient,
      tracePair,mul_zero,Complex.zero_re,AddChar.map_zero_eq_one,Circle.coe_one,mul_one]
    ring

lemma cubicThetaAdditiveCoefficient_series (z : ℂ) (v : ℝ) :
    cubicThetaNonconstant (cubicThetaAdditiveCoefficient z) (0,v)=
      cubicThetaNonconstant cubicThetaArithmeticCoefficient (z,v) := by
  unfold cubicThetaNonconstant
  exact tsum_congr (cubicThetaAdditiveCoefficient_term z v)

theorem cubicThetaAdditive_mellin (z : ℂ) {s : ℂ} (hs : 2<s.re) :
    mellin (fun v : ℝ => cubicThetaNonconstant cubicThetaArithmeticCoefficient (z,v)) s=
      mellin cubicThetaWhittaker s*cubicThetaDirichlet (cubicThetaAdditiveCoefficient z) s := by
  simp_rw [←cubicThetaAdditiveCoefficient_series z]
  exact cubicThetaNonconstant_mellin (by norm_num) (cubicThetaAdditiveCoefficient_norm z) hs

theorem cubicThetaLevelCompleted_dirichlet {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) {s : ℂ} (hs : 2<s.re) :
    cubicThetaLevelCompleted q x y s=
      (cubicThetaLevelScale q:ℂ)^(-s)*mellin cubicThetaWhittaker s*
        cubicThetaDirichlet (cubicThetaAdditiveCoefficient (3*(x:ℂ)/(q:ℂ))) s := by
  rw [←cubicThetaLevelCompleted_mellin hq x y hxy (by linarith)]
  change mellin (fun t : ℝ => cubicThetaNonconstant cubicThetaArithmeticCoefficient
    (3*(x:ℂ)/(q:ℂ),cubicThetaLevelScale q*t)) s=_
  rw [mellin_comp_mul_left (fun v : ℝ => cubicThetaNonconstant cubicThetaArithmeticCoefficient
      (3*(x:ℂ)/(q:ℂ),v)) s (cubicThetaLevelScale_pos hq),
    cubicThetaAdditive_mellin _ hs]
  simp only [smul_eq_mul,mul_assoc]

end CubicFirstMoment

end

end OAI
