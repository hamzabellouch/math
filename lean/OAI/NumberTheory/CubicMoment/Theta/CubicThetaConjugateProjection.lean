import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSieveProjection

namespace OAI

/-! The finite projection expressed in the original conjugate theta
function, including cancellation of its constant term. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaWhittaker_star (v : ℝ) : star (cubicThetaWhittaker v) = cubicThetaWhittaker v := by
  have he : cubicThetaWhittaker v = ((v/2*cubicBesselKernel ((2*Real.pi*v)^2):ℝ):ℂ) := by
    simp only [cubicThetaWhittaker,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
  rw [he]
  exact Complex.conj_ofReal _

lemma cubicThetaSeriesTerm_star_reflect (a : Eisenstein → ℂ) (n : Eisenstein) (z : ℂ) (v : ℝ) :
    star (cubicThetaSeriesTerm a (-z) v n) =
      cubicThetaSeriesTerm (fun n => star (a n)) z v n := by
  by_cases hn : n = 0
  · simp [cubicThetaSeriesTerm,hn]
  · have he : tracePair (cubicThetaFrequency n) (-z) =
        -tracePair (cubicThetaFrequency n) z := by
      simp only [tracePair,mul_neg,Complex.neg_re,mul_neg]
    simp only [cubicThetaSeriesTerm,hn,ite_false,star_mul,cubicThetaWhittaker_star,he,
      AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
    change _ = _
    simp only [←Complex.star_def,star_star]
    ring

lemma cubicThetaNonconstant_star_reflect (a : Eisenstein → ℂ) (z : ℂ) (v : ℝ) :
    star (cubicThetaNonconstant a (-z,v)) =
      cubicThetaNonconstant (fun n => star (a n)) (z,v) := by
  unfold cubicThetaNonconstant
  rw [tsum_star]
  exact tsum_congr (fun n => cubicThetaSeriesTerm_star_reflect a n z v)

lemma cubicThetaFunction_conjugate_expansion (z : ℂ) (v : ℝ) :
    star (cubicThetaFunction (z,v)) =
      ((cubicThetaConstant*v^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaConjugateCoefficient (z,v) := by
  rw [←cubicThetaFunction_even z v]
  unfold cubicThetaFunction cubicThetaAuxiliarySeries
  rw [cubicThetaCuspCoefficient_zero,star_add,cubicThetaNonconstant_star_reflect]
  simp only [Complex.star_def,Complex.conj_ofReal]
  rfl

/-- The literal translated-theta projection in DR v3 (5.18). The
constant term cancels by 1+omega+omega^2=0. -/
theorem cubicThetaSelected_conjugate_projection (z : ℂ) {v : ℝ} (hv : 0 < v) :
    cubicThetaNonconstant cubicThetaSelectedCoefficient (z,v) =
      (star (cubicThetaFunction (z,v))+
        omega*star (cubicThetaFunction (z+omega,v))+
        omega^2*star (cubicThetaFunction (z+2*omega,v)))/3 := by
  rw [cubicThetaSelected_projection z hv]
  simp only [cubicThetaFunction_conjugate_expansion]
  linear_combination -((cubicThetaConstant*v^(2/3:ℝ):ℝ):ℂ)/3*omega_quadratic

end CubicFirstMoment

end

end OAI
