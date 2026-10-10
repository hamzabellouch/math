import OAI.MeasureTheory.Falconer.Angular.StationaryJetOperators
import OAI.MeasureTheory.Falconer.Angular.LocalizedStationaryExpansion

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem fresnelCoefficient_half {Λ : ℝ} (hΛ : 0 < Λ) :
    fresnelCoefficient (Λ/2) = ((Λ^(-1/2:ℝ):ℝ):ℂ) *
      ((Real.sqrt (2*Real.pi):ℂ)*Complex.exp (-(Real.pi:ℂ)/4*Complex.I)) := by
  have he : Real.pi/(Λ/2) = (2*Real.pi)/Λ := by ring
  have hp : (Real.pi/(Λ/2))^(1/2:ℝ) = Λ^(-1/2:ℝ)*Real.sqrt (2*Real.pi) := by
    rw [he,Real.div_rpow (by positivity) hΛ.le,Real.sqrt_eq_rpow]
    rw [show (-1/2:ℝ) = -(1/2:ℝ) by ring,Real.rpow_neg hΛ.le]
    ring
  simp only [fresnelCoefficient,hp,Complex.ofReal_mul]
  ring

 theorem quadratic_coefficient_normalization (k : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) (d : ℂ) :
    ((((k.factorial:ℝ)⁻¹*(Real.pi^2/(Λ/2))^k):ℝ):ℂ)*Complex.I^k *
      (((-2*(Real.pi:ℂ)*Complex.I)^(2*k))⁻¹*d) =
    ((Λ⁻¹:ℝ):ℂ)^k * (((k.factorial:ℝ)⁻¹:ℝ):ℂ) * (-Complex.I/2)^k*d := by
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΛ' : (Λ:ℂ) ≠ 0 := by exact_mod_cast hΛ.ne'
  have he : (((Real.pi^2/(Λ/2):ℝ):ℂ)*Complex.I*((-2*(Real.pi:ℂ)*Complex.I)^2)⁻¹) =
      ((Λ⁻¹:ℝ):ℂ)*(-Complex.I/2) := by
    push_cast
    field_simp
    simp [Complex.I_sq]
  calc
    _ = (((k.factorial:ℝ)⁻¹:ℝ):ℂ) *
        ((((Real.pi^2/(Λ/2):ℝ):ℂ)*Complex.I*((-2*(Real.pi:ℂ)*Complex.I)^2)⁻¹)^k) * d := by
      simp only [Complex.ofReal_mul,Complex.ofReal_pow,mul_pow,inv_pow,pow_mul]
      ring
    _ = _ := by rw [he,mul_pow]; ring

 theorem stationary_expansion_direct_operators {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    fresnelCoefficient (Λ/2) * stationaryDerivativeExpansion f n Λ =
      ((Λ^(-1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
        ((Λ⁻¹:ℝ):ℂ)^j * directStationaryOperator j f 0 := by
  rw [fresnelCoefficient_half hΛ,stationaryDerivativeExpansion,mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [quadratic_coefficient_normalization j hΛ,stationaryAmplitude_jet (2*j) hf]
  simp only [directStationaryOperator,add_zero]
  ring

end PlanarFalconer

end OAI
