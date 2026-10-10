import OAI.MeasureTheory.Falconer.Angular.StationaryChartAmplitude
import Mathlib.Analysis.Complex.Exponential

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def localizedCircleIntegral (Λ : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ θ in stationarySineInverse (-1)..stationarySineInverse 1,
    Complex.exp (Complex.I*(Λ:ℂ)*(Real.cos θ:ℂ)) *
      (stationaryCutoff (stationarySineChart θ) : ℂ) * f θ

 theorem stationaryAmplitude_support (f : ℝ → ℂ) :
    Function.support (stationaryAmplitude f) ⊆ Ioo (-1:ℝ) 1 := by
  intro u hu
  have hw : stationaryCutoff u ≠ 0 := by
    intro h
    exact hu (by simp [stationaryAmplitude,stationaryWeight,h])
  have hh : u ∈ Metric.ball (0:ℝ) 1 := by
    change u ∈ Function.support (stationaryCutoff : ℝ → ℝ) at hw
    rw [ContDiffBump.support_eq] at hw
    exact hw
  simpa [Real.ball_eq_Ioo] using hh

 theorem localizedCircleIntegral_quadratic (Λ : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    localizedCircleIntegral Λ f = Complex.exp (Complex.I*(Λ:ℂ)) *
      ∫ u : ℝ, Complex.exp (-(((Λ/2:ℝ):ℂ)*Complex.I)*(u:ℂ)^2) * stationaryAmplitude f u := by
  let F : ℝ → ℂ := fun θ => Complex.exp (Complex.I*(Λ:ℂ)*(Real.cos θ:ℂ)) *
    (stationaryCutoff (stationarySineChart θ) : ℂ) * f θ
  have hchart : Continuous stationarySineChart := by
    unfold stationarySineChart
    fun_prop
  have hF : Continuous F := by
    apply Continuous.mul _ hf
    apply Continuous.mul
    · exact Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_cos))
    · exact Complex.continuous_ofReal.comp (stationaryCutoff.continuous.comp hchart)
  change (∫ θ in stationarySineInverse (-1)..stationarySineInverse 1, F θ) = _
  rw [← stationarySine_substitution (by norm_num : (-2:ℝ) < -1) (by norm_num) (by norm_num) F hF]
  have he : (∫ u in (-1:ℝ)..1, (stationarySineJacobian u : ℂ)*F (stationarySineInverse u)) =
      ∫ u in (-1:ℝ)..1, Complex.exp (Complex.I*(Λ:ℂ)) *
        (Complex.exp (-(((Λ/2:ℝ):ℂ)*Complex.I)*(u:ℂ)^2)*stationaryAmplitude f u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (-1:ℝ) 1 := by simpa using hu
    have hu2 : u ∈ Icc (-2:ℝ) 2 := ⟨by linarith [hu'.1],by linarith [hu'.2]⟩
    dsimp [F]
    rw [stationarySineInverse_cos hu2,stationarySineChart_inverse hu2,
      stationaryAmplitude_eq hu']
    have hp : Complex.I*(Λ:ℂ)*((1-u^2/2:ℝ):ℂ) =
        Complex.I*(Λ:ℂ) + -(((Λ/2:ℝ):ℂ)*Complex.I)*(u:ℂ)^2 := by
      push_cast
      ring
    rw [hp,Complex.exp_add]
    ring
  rw [he,intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro u hu
  have hs : u ∈ Ioo (-1:ℝ) 1 := stationaryAmplitude_support f (by
    intro h
    exact hu (by simp [h]))
  exact ⟨hs.1,hs.2.le⟩

end PlanarFalconer

end OAI
