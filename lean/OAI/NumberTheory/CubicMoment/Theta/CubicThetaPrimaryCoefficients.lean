import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmetic

namespace OAI

/-! The exact primary cube coefficients isolated in DR v3 (5.17).
This connects the constructed theta expansion to the completed Gauss sum. -/
noncomputable section
namespace CubicFirstMoment

/-- The primary frequency lambda^-3*c*d^3 has no unit phase and has the
normalized conjugate Gauss coefficient of the original cubic sum. -/
lemma cubicThetaArithmeticCoefficient_primary {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    cubicThetaArithmeticCoefficient (lambdaE*c*d^3) =
      ((81/(Real.sqrt (norm c)*norm d):ℝ):ℂ)*star (gauss c) := by
  let R : CubicThetaCoordinates (lambdaE*c*d^3) := {
    unit := 1
    order := 1
    squarefreePart := c
    cubePart := d
    squarefree_primary := hc
    cube_primary := hd
    squarefree := hs
    numerator_eq := by simp [mul_assoc] }
  rw [cubicThetaArithmeticCoefficient_formula R]
  norm_num [R,CubicThetaCoordinates.coefficient,CubicThetaCoordinates.amplitude]

/-- Conjugating the primary coefficient gives the original Gauss sum,
with the exact real normalization retained. -/
lemma cubicThetaArithmeticCoefficient_primary_conj {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    star (cubicThetaArithmeticCoefficient (lambdaE*c*d^3)) =
      ((81/(Real.sqrt (norm c)*norm d):ℝ):ℂ)*gauss c := by
  rw [cubicThetaArithmeticCoefficient_primary hc hd hs,star_mul,star_star]
  simp only [Complex.star_def,Complex.conj_ofReal]
  ring

/-- The source uses `tau(mu)`, while our Whittaker coefficient is
`tau(mu)/|mu|`. -/
def cubicThetaTau (n : Eisenstein) : ℂ :=
  (‖cubicThetaFrequency n‖:ℂ)*cubicThetaArithmeticCoefficient n

lemma cubicThetaFrequency_primary_norm (c d : Eisenstein) :
    ‖cubicThetaFrequency (lambdaE*c*d^3)‖ =
      Real.sqrt 3*Real.sqrt (norm c)*(Real.sqrt (norm d))^3/9 := by
  have hcN := norm_nonneg c
  have hdN := norm_nonneg d
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (by positivity)).mp
  rw [cubicThetaFrequency_sq]
  have he : norm (lambdaE*c*d^3) = 3*norm c*norm d^3 := by
    change Complex.normSq (((lambdaE*c*d^3:Eisenstein):ℂ)) = _
    simp only [Subalgebra.coe_mul,Subalgebra.coe_pow,Complex.normSq_mul,
      map_pow,lambdaE_coe,traceLambda_normSq]
    rfl
  rw [he]
  calc
    _ = (Real.sqrt 3)^2*(Real.sqrt (norm c))^2*
        ((Real.sqrt (norm d))^2)^3/81 := by
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sq_sqrt hcN,Real.sq_sqrt hdN]
    _ = _ := by ring

/-- DR v3 (5.17), with the unnormalized theta coefficient restored. -/
theorem cubicThetaTau_primary_conj {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    star (cubicThetaTau (lambdaE*c*d^3)) =
      ((3^(5/2:ℝ)*Real.sqrt (norm d):ℝ):ℂ)*gauss c := by
  have hcN : 0 < Real.sqrt (norm c) := Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hc))
  have hdN : 0 < norm d := norm_pos_of_ne_zero (primary_ne_zero hd)
  have hp : (3:ℝ)^(5/2:ℝ) = 9*Real.sqrt 3 := by
    rw [show (5/2:ℝ) = 2+1/2 by norm_num,Real.rpow_add (by norm_num : (0:ℝ) < 3),
      Real.rpow_two,←Real.sqrt_eq_rpow]
    norm_num
  have ha : ‖cubicThetaFrequency (lambdaE*c*d^3)‖*
      (81/(Real.sqrt (norm c)*norm d)) = 3^(5/2:ℝ)*Real.sqrt (norm d) := by
    rw [cubicThetaFrequency_primary_norm c d,hp]
    field_simp
    have hdS := Real.sq_sqrt hdN.le
    nlinarith [sq_nonneg (Real.sqrt (norm d))]
  rw [cubicThetaTau,star_mul,cubicThetaArithmeticCoefficient_primary_conj hc hd hs]
  simp only [Complex.star_def,Complex.conj_ofReal]
  calc
    _ = ((‖cubicThetaFrequency (lambdaE*c*d^3)‖*
        (81/(Real.sqrt (norm c)*norm d)):ℝ):ℂ)*gauss c := by push_cast; ring
    _ = _ := by rw [ha]

end CubicFirstMoment

end

end OAI
