import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSieveSupport

namespace OAI

/-! The primary cubic Gauss coefficients are the exact finite additive
projection of the conjugate cubic theta expansion. No transformation under
inversion is used in this arithmetic sieving step. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaConjugateCoefficient (n : Eisenstein) : ℂ := star (cubicThetaArithmeticCoefficient n)

def cubicThetaSelectedCoefficient (n : Eisenstein) : ℂ :=
  if cubicThetaPrimarySupport n then cubicThetaConjugateCoefficient n else 0

lemma cubicThetaConjugateCoefficient_norm (n : Eisenstein) :
    ‖cubicThetaConjugateCoefficient n‖ ≤ 81 := by
  simpa only [cubicThetaConjugateCoefficient,norm_star] using cubicThetaArithmeticCoefficient_norm_le n

lemma cubicThetaSelectedCoefficient_norm (n : Eisenstein) :
    ‖cubicThetaSelectedCoefficient n‖ ≤ 81 := by
  unfold cubicThetaSelectedCoefficient
  split_ifs
  · exact cubicThetaConjugateCoefficient_norm n
  · norm_num

lemma cubicThetaSeriesTerm_translate (a : Eisenstein → ℂ) (n : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaSeriesTerm a (z+omega) v n =
      cubicThetaSievePhase n*cubicThetaSeriesTerm a z v n := by
  by_cases hn : n = 0
  · simp [cubicThetaSeriesTerm,hn]
  · have he : tracePair (cubicThetaFrequency n) (z+omega) =
        tracePair (cubicThetaFrequency n) z+tracePair (cubicThetaFrequency n) omega := by
      simp only [tracePair,mul_add,Complex.add_re]
    simp only [cubicThetaSeriesTerm,hn,ite_false,he,
      AddChar.map_add_eq_mul,Circle.coe_mul,cubicThetaSievePhase]
    ring

lemma cubicThetaSeriesTerm_translate_twice (a : Eisenstein → ℂ) (n : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaSeriesTerm a (z+2*omega) v n =
      cubicThetaSievePhase n^2*cubicThetaSeriesTerm a z v n := by
  rw [show z+2*omega = (z+omega)+omega by ring,
    cubicThetaSeriesTerm_translate,cubicThetaSeriesTerm_translate]
  ring

lemma cubicThetaSelected_term (n : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaSeriesTerm cubicThetaSelectedCoefficient z v n =
      (cubicThetaSeriesTerm cubicThetaConjugateCoefficient z v n+
        omega*cubicThetaSeriesTerm cubicThetaConjugateCoefficient (z+omega) v n+
        omega^2*cubicThetaSeriesTerm cubicThetaConjugateCoefficient (z+2*omega) v n)/3 := by
  rw [cubicThetaSeriesTerm_translate,cubicThetaSeriesTerm_translate_twice]
  by_cases hn : n = 0
  · simp [cubicThetaSeriesTerm,hn]
  · have he : cubicThetaSelectedCoefficient n =
        cubicThetaRootProjector (cubicThetaSievePhase n)*cubicThetaConjugateCoefficient n :=
      (cubicThetaRootProjector_arithmetic n).symm
    simp only [cubicThetaSeriesTerm,hn,ite_false,he,cubicThetaRootProjector]
    ring

/-- The exact finite translate formula for the series supported on S. -/
theorem cubicThetaSelected_projection (z : ℂ) {v : ℝ} (hv : 0 < v) :
    cubicThetaNonconstant cubicThetaSelectedCoefficient (z,v) =
      (cubicThetaNonconstant cubicThetaConjugateCoefficient (z,v)+
        omega*cubicThetaNonconstant cubicThetaConjugateCoefficient (z+omega,v)+
        omega^2*cubicThetaNonconstant cubicThetaConjugateCoefficient (z+2*omega,v))/3 := by
  have hs (w : ℂ) : Summable (cubicThetaSeriesTerm cubicThetaConjugateCoefficient w v) :=
    cubicThetaSeries_summable (by norm_num : (0:ℝ) ≤ 81)
      (fun n hn => (cubicThetaConjugateCoefficient_norm n).trans
        (le_mul_of_one_le_right (by norm_num) (one_le_norm hn))) hv w
  unfold cubicThetaNonconstant
  calc
    _ = ∑' n : Eisenstein,
        (cubicThetaSeriesTerm cubicThetaConjugateCoefficient z v n+
          omega*cubicThetaSeriesTerm cubicThetaConjugateCoefficient (z+omega) v n+
          omega^2*cubicThetaSeriesTerm cubicThetaConjugateCoefficient (z+2*omega) v n)/3 :=
      tsum_congr (fun n => cubicThetaSelected_term n z v)
    _ = _ := by
      rw [tsum_div_const,((hs z).add ((hs (z+omega)).mul_left omega)).tsum_add
        ((hs (z+2*omega)).mul_left (omega^2)),
        (hs z).tsum_add ((hs (z+omega)).mul_left omega),tsum_mul_left,tsum_mul_left]

end CubicFirstMoment

end

end OAI
