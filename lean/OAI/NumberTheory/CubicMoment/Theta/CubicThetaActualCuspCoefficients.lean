import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspTypes
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConjugateProjection

namespace OAI

/-! Literal constant and nonconstant coefficients of the three actual
cusp types, and their conjugates on the common frequency lattice. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaActualCuspCoefficient (n : ℤ) : Eisenstein → ℂ :=
  if (3:ℤ) ∣ n then cubicThetaArithmeticCoefficient else cubicThetaShiftedLatticeCoefficient n

def cubicThetaActualCuspConstant (n : ℤ) : ℂ :=
  if (3:ℤ) ∣ n then cubicThetaSeriesConstant else 0

lemma cubicThetaCuspExpansion_coefficients (n : ℤ) (p : ℂ×ℝ) :
    cubicThetaCuspExpansion n p=cubicThetaActualCuspConstant n*((p.2^(2/3:ℝ):ℝ):ℂ)+
      cubicThetaNonconstant (cubicThetaActualCuspCoefficient n) p := by
  by_cases hn : (3:ℤ) ∣ n <;>
    simp [cubicThetaCuspExpansion,cubicThetaActualCuspConstant,cubicThetaActualCuspCoefficient,hn]

lemma cubicThetaActualCuspCoefficient_bound (n : ℤ) (k : Eisenstein) :
    ‖cubicThetaActualCuspCoefficient n k‖≤243 := by
  unfold cubicThetaActualCuspCoefficient
  split_ifs
  · exact (cubicThetaArithmeticCoefficient_norm_le k).trans (by norm_num)
  · exact cubicThetaShiftedLatticeCoefficient_bound n k

lemma cubicThetaSeriesTerm_reflect (a : Eisenstein→ℂ) (n : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaSeriesTerm a (-z) v (-n)=
      cubicThetaSeriesTerm (fun k => a (-k)) z v n := by
  by_cases hn : n=0
  · simp [cubicThetaSeriesTerm,hn]
  · have hf : cubicThetaFrequency (-n)= -cubicThetaFrequency n := by
      simp only [cubicThetaFrequency,Subalgebra.coe_neg,neg_div]
    have ht : tracePair (-cubicThetaFrequency n) (-z)=tracePair (cubicThetaFrequency n) z := by
      simp only [tracePair,neg_mul_neg]
    simp only [cubicThetaSeriesTerm,ite_eq_right hn,ite_eq_right (neg_ne_zero.mpr hn),hf,
      norm_neg,ht]

lemma cubicThetaNonconstant_reflect (a : Eisenstein→ℂ) (z : ℂ) (v : ℝ) :
    cubicThetaNonconstant a (-z,v)=cubicThetaNonconstant (fun k => a (-k)) (z,v) := by
  unfold cubicThetaNonconstant
  rw [←(Equiv.neg Eisenstein).tsum_eq (fun k => cubicThetaSeriesTerm a (-z) v k)]
  exact tsum_congr (fun k => cubicThetaSeriesTerm_reflect a k z v)

lemma cubicThetaNonconstant_star (a : Eisenstein→ℂ) (z : ℂ) (v : ℝ) :
    star (cubicThetaNonconstant a (z,v))=
      cubicThetaNonconstant (fun k => star (a (-k))) (z,v) := by
  have he := cubicThetaNonconstant_star_reflect a (-z) v
  rw [neg_neg] at he
  exact he.trans (cubicThetaNonconstant_reflect (fun k => star (a k)) z v)

lemma cubicThetaNormalizedSeries_conjugate (p : CubicThetaPoint) :
    star (cubicThetaNormalizedSeriesSection.val p)=
      star cubicThetaSeriesConstant*((p.val.2^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaConjugateCoefficient p.val := by
  rw [cubicThetaNormalizedSeriesSection_apply,star_add,star_mul]
  have he := cubicThetaNonconstant_star_reflect cubicThetaArithmeticCoefficient p.val.1 p.val.2
  rw [cubicThetaArithmetic_even] at he
  rw [he]
  simp only [Complex.star_def,Complex.conj_ofReal,mul_comm]
  rfl

lemma cubicThetaCuspExpansion_conjugate (n : ℤ) (p : ℂ×ℝ) :
    star (cubicThetaCuspExpansion n p)=
      star (cubicThetaActualCuspConstant n)*((p.2^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant (fun k => star (cubicThetaActualCuspCoefficient n (-k))) p := by
  rcases p with ⟨z,v⟩
  rw [cubicThetaCuspExpansion_coefficients,star_add,star_mul,cubicThetaNonconstant_star]
  simp only [Complex.star_def,Complex.conj_ofReal,mul_comm]

end CubicFirstMoment

end

end OAI
