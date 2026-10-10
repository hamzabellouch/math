import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCircleExtraction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularFrequency

namespace OAI

/-! The actual trace character on a small horizontal circle, with both orientations. -/
noncomputable section
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

lemma cubicThetaCirclePhase_trace (w : ℂ) (r : ℝ) (t : AddCircle (1:ℝ)) :
    cubicThetaCirclePhase w r t=
      (Real.fourierChar (tracePair w ((r:ℂ)*fourier 1 t)):ℂ) := by
  rw [Real.fourierChar_apply]
  unfold cubicThetaCirclePhase
  rw [cubicThetaCircleLinear_real]
  congr 1
  simp only [tracePair,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  push_cast
  ring

lemma cubicThetaCirclePhase_trace_reverse (w : ℂ) (r : ℝ) (t : AddCircle (1:ℝ)) :
    cubicThetaCirclePhase (star w) r t=
      (Real.fourierChar (tracePair w ((r:ℂ)*fourier (-1) t)):ℂ) := by
  rw [cubicThetaCirclePhase_trace,fourier_neg]
  congr 2
  simp only [tracePair,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma cubicThetaSeriesTerm_add (a : Eisenstein→ℂ) (z u : ℂ) (v : ℝ) (n : Eisenstein) :
    cubicThetaSeriesTerm a (z+u) v n=cubicThetaSeriesTerm a z v n*
      (Real.fourierChar (tracePair (cubicThetaFrequency n) u):ℂ) := by
  by_cases hn : n=0
  · simp [cubicThetaSeriesTerm,hn]
  have ht : tracePair (cubicThetaFrequency n) (z+u)=
      tracePair (cubicThetaFrequency n) z+tracePair (cubicThetaFrequency n) u := by
    simp only [tracePair,mul_add,Complex.add_re]
  simp only [cubicThetaSeriesTerm,hn,ite_false,ht,AddChar.map_add_eq_mul,Circle.coe_mul]
  ring

lemma cubicThetaSeriesTerm_circle (a : Eisenstein→ℂ) (z d : ℂ) (r v : ℝ)
    (n : Eisenstein) (t : AddCircle (1:ℝ)) :
    cubicThetaSeriesTerm a (z+(r:ℂ)*d*fourier 1 t) v n=
      cubicThetaSeriesTerm a z v n*cubicThetaCirclePhase (cubicThetaFrequency n*d) r t := by
  rw [cubicThetaSeriesTerm_add,cubicThetaCirclePhase_trace]
  congr 2
  simp only [tracePair,mul_assoc,mul_comm,mul_left_comm]
  rfl

lemma cubicThetaSeriesTerm_circle_reverse (a : Eisenstein→ℂ) (z d : ℂ) (r v : ℝ)
    (n : Eisenstein) (t : AddCircle (1:ℝ)) :
    cubicThetaSeriesTerm a (z+(r:ℂ)*d*fourier (-1) t) v n=
      cubicThetaSeriesTerm a z v n*cubicThetaCirclePhase (star (cubicThetaFrequency n*d)) r t := by
  rw [cubicThetaSeriesTerm_add,cubicThetaCirclePhase_trace_reverse]
  congr 2
  simp only [tracePair,mul_assoc,mul_comm,mul_left_comm]
  rfl

lemma cubicThetaSeriesTerm_frequency_power (a : Eisenstein→ℂ) (z : ℂ) (v : ℝ)
    (n : Eisenstein) (k : ℕ) :
    cubicThetaSeriesTerm a z v n*cubicThetaFrequency n^k=
      cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (k:ℤ)) z v n := by
  by_cases hn : n=0
  · simp [cubicThetaSeriesTerm,hn]
  simp only [cubicThetaSeriesTerm,hn,ite_false,cubicThetaAngularCoefficient_nat]
  ring

lemma cubicThetaSeriesTerm_conj_frequency_power (a : Eisenstein→ℂ) (z : ℂ) (v : ℝ)
    (n : Eisenstein) (k : ℕ) :
    cubicThetaSeriesTerm a z v n*star (cubicThetaFrequency n)^k=
      cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (-(k:ℤ))) z v n := by
  by_cases hn : n=0
  · simp [cubicThetaSeriesTerm,hn]
  simp only [cubicThetaSeriesTerm,hn,ite_false,cubicThetaAngularCoefficient_neg_nat]
  ring

end CubicFirstMoment

end

end OAI
