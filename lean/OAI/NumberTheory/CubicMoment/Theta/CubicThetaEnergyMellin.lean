import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMassResidue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Absolute Fubini for the actual horizontal Fourier energy and its
coefficient Dirichlet mass. The frequency dilation is retained exactly. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment
local instance : Countable Eisenstein := coordinatesEquiv.symm.injective.countable

def cubicThetaEnergyMellinTerm (σ : ℝ) (n : Eisenstein) (v : ℝ) : ℝ :=
  v^(2*σ-1)*‖cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n‖^2

lemma cubicThetaEnergyMellinTerm_nonneg (σ : ℝ) (n : Eisenstein) {v : ℝ}
    (hv : 0 < v) : 0 ≤ cubicThetaEnergyMellinTerm σ n v :=
  mul_nonneg (Real.rpow_nonneg hv.le _) (sq_nonneg _)

lemma cubicThetaEnergyMellinTerm_integrable {σ : ℝ} (hσ : 0 ≤ σ) (n : Eisenstein) :
    IntegrableOn (cubicThetaEnergyMellinTerm σ n) (Ioi 0) := by
  by_cases hn : n=0
  · subst n
    have hz : IntegrableOn (fun _ : ℝ => (0:ℝ)) (Ioi 0) (volume : Measure ℝ) := integrableOn_zero
    convert hz using 1
    ext v
    simp [cubicThetaEnergyMellinTerm,cubicThetaSeriesTerm]
  · have hi := (cubicWhittakerEnergy_scaled_integrable hσ (cubicThetaFrequency_pos hn)).const_mul
      (‖cubicThetaArithmeticCoefficient n‖^2)
    apply hi.congr
    filter_upwards with v
    simp only [cubicThetaEnergyMellinTerm,cubicThetaSeriesTerm,ite_eq_right hn,
      norm_mul,Circle.norm_coe,mul_one,mul_pow]
    ring

lemma cubicThetaEnergyMellinTerm_integral (σ : ℝ) (n : Eisenstein) :
    (∫ v in Ioi (0:ℝ), cubicThetaEnergyMellinTerm σ n v)=
      (81^σ*cubicWhittakerEnergyMass σ)*cubicThetaCoefficientMassTerm σ n := by
  by_cases hn : n=0
  · subst n
    have hz : ¬Nonempty (CubicThetaCoordinates (0:Eisenstein)) := by
      rintro ⟨R⟩
      exact R.ne_zero rfl
    simp [cubicThetaEnergyMellinTerm,cubicThetaSeriesTerm,
      cubicThetaCoefficientMassTerm,cubicThetaArithmeticCoefficient,hz]
  · calc
      _ = ‖cubicThetaArithmeticCoefficient n‖^2 *
          (∫ v in Ioi (0:ℝ), v^(2*σ-1)*‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖^2) := by
        rw [←integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v _
        simp only [cubicThetaEnergyMellinTerm,cubicThetaSeriesTerm,ite_eq_right hn,
          norm_mul,Circle.norm_coe,mul_one,mul_pow]
        ring
      _ = _ := by
        rw [cubicWhittakerEnergy_mass_scale σ (cubicThetaFrequency_pos hn),cubicThetaFrequency_rpow hn]
        rw [show -(-2*σ)/2=σ by ring,show (-2*σ)/2= -σ by ring]
        unfold cubicThetaCoefficientMassTerm
        ring

lemma cubicThetaEnergyMellinTerm_norm_integral (σ : ℝ) (n : Eisenstein) :
    (∫ v in Ioi (0:ℝ), ‖cubicThetaEnergyMellinTerm σ n v‖)=
      (81^σ*cubicWhittakerEnergyMass σ)*cubicThetaCoefficientMassTerm σ n := by
  rw [←cubicThetaEnergyMellinTerm_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  exact Real.norm_of_nonneg (cubicThetaEnergyMellinTerm_nonneg σ n hv)

lemma cubicThetaArithmeticFourierEnergy_all (v : ℝ) :
    cubicThetaArithmeticFourierEnergy v=
      ∑' n : Eisenstein, ‖cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n‖^2 := by
  let f (n : Eisenstein) : ℝ := ‖cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n‖^2
  have hs : Function.support f ⊆ Set.range (fun h : Eisenstein => -lambdaE*h) := by
    intro n hn
    apply cubicThetaSeriesTerm_row_support 0 v
    intro hz
    exact hn (by simp only [f,hz,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)])
  have he := cubicThetaRowIndex_injective.tsum_eq hs
  simpa only [f,←cubicThetaArithmeticRowTerm_eq,cubicThetaArithmeticFourierEnergy] using he

theorem cubicThetaArithmeticFourierEnergy_mellin {σ : ℝ} (hσ : 0 < σ) :
    (∫ v in Ioi (0:ℝ), v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v)=
      81^σ*cubicWhittakerEnergyMass σ*cubicThetaCoefficientMass σ := by
  have hi := fun n => cubicThetaEnergyMellinTerm_integrable hσ.le n
  have hs : Summable (fun n : Eisenstein =>
      ∫ v in Ioi (0:ℝ), ‖cubicThetaEnergyMellinTerm σ n v‖) := by
    simpa only [cubicThetaEnergyMellinTerm_norm_integral] using
      (cubicThetaCoefficientMassTerm_summable hσ).mul_left (81^σ*cubicWhittakerEnergyMass σ)
  calc
    _ = ∫ v in Ioi (0:ℝ), ∑' n : Eisenstein, cubicThetaEnergyMellinTerm σ n v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      dsimp only
      rw [cubicThetaArithmeticFourierEnergy_all,←tsum_mul_left]
      rfl
    _ = ∑' n : Eisenstein, ∫ v in Ioi (0:ℝ), cubicThetaEnergyMellinTerm σ n v :=
      (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = _ := by
      simp_rw [cubicThetaEnergyMellinTerm_integral]
      rw [tsum_mul_left]
      rfl

end CubicFirstMoment

end

end OAI
