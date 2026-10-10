import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryPeriodicity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueNormalization

namespace OAI

/-! Reindex the literal theta expansion on the actual three-Eisenstein
period lattice. Coefficients off this lattice vanish by their ramified
support, so this change of variables introduces no multiplicity. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaRowIndex_injective :
    Function.Injective (fun h : Eisenstein => -lambdaE*h) := by
  intro h k he
  exact mul_left_cancel₀ (neg_ne_zero.mpr lambdaE_prime.ne_zero) he

lemma cubicThetaSeriesTerm_row_support (z : ℂ) (v : ℝ) :
    Function.support (cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v) ⊆
      Set.range (fun h : Eisenstein => -lambdaE*h) := by
  intro n hn
  have ha : cubicThetaArithmeticCoefficient n≠0 := by
    intro hz
    exact hn (by simp [cubicThetaSeriesTerm,hz])
  obtain ⟨h,hh⟩ := cubicThetaArithmeticCoefficient_lambda_dvd ha
  exact ⟨-h,by simpa using hh.symm⟩

def cubicThetaArithmeticRowTerm (z : ℂ) (v : ℝ) (h : Eisenstein) : ℂ :=
  if h=0 then 0 else cubicThetaArithmeticCoefficient (-lambdaE*h)*
    cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v)*
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)

lemma cubicThetaArithmeticRowTerm_eq (z : ℂ) (v : ℝ) (h : Eisenstein) :
    cubicThetaArithmeticRowTerm z v h=
      cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v (-lambdaE*h) := by
  by_cases hh : h=0
  · simp [cubicThetaArithmeticRowTerm,cubicThetaSeriesTerm,hh]
  · have hn : -lambdaE*h≠0 := mul_ne_zero (neg_ne_zero.mpr lambdaE_prime.ne_zero) hh
    simp only [cubicThetaArithmeticRowTerm,cubicThetaSeriesTerm,hh,hn,ite_false,
      cubicThetaRowFrequency_index]
    congr 3
    unfold tracePair
    rw [mul_comm z (cubicThetaRowFrequency h)]

theorem cubicThetaArithmeticRowSeries (z : ℂ) (v : ℝ) :
    cubicThetaNonconstant cubicThetaArithmeticCoefficient (z,v)=
      ∑' h : Eisenstein,cubicThetaArithmeticRowTerm z v h := by
  simp_rw [cubicThetaArithmeticRowTerm_eq]
  exact (cubicThetaRowIndex_injective.tsum_eq
    (cubicThetaSeriesTerm_row_support z v)).symm

lemma cubicThetaArithmeticRowTerm_summable (z : ℂ) {v : ℝ} (hv : 0<v) :
    Summable (cubicThetaArithmeticRowTerm z v) := by
  simpa only [Function.comp_def,←cubicThetaArithmeticRowTerm_eq] using
    (cubicThetaArithmetic_summable hv z).comp_injective cubicThetaRowIndex_injective

lemma cubicThetaArithmeticRowTerm_phase (z : ℂ) (v : ℝ) (h : Eisenstein) :
    cubicThetaArithmeticRowTerm z v h=cubicThetaArithmeticRowTerm 0 v h*
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ) := by
  by_cases hh : h=0
  · simp [cubicThetaArithmeticRowTerm,hh]
  · simp [cubicThetaArithmeticRowTerm,hh,tracePair]

end CubicFirstMoment

end

end OAI
