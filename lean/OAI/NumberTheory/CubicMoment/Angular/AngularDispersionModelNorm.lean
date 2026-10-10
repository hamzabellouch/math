import OAI.NumberTheory.CubicMoment.Angular.AngularDispersionModelEnergy
import OAI.NumberTheory.CubicMoment.Estimates.DispersionModelEnergy

namespace OAI

/-! A linear-size bound for the literal model polynomial, used when
multiplying the Type-I error by the correction coefficient. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_logarithmic_dispersionModel_norm {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R : ℝ} (hR : 1 ≤ R) (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (K : ℝ) (a : ℕ), 0 < K ∧ ∀ r X e u,
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ‖dispersionModel (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u‖ ≤
        K*(L r)^(5/6:ℝ)*(1+Real.log (L r))^a := by
  obtain ⟨E,a,hE,henergy⟩ := angular_logarithmic_dispersionModel_energy ℓ hW hR hlo hhi
  refine ⟨E+1,a,by positivity,?_⟩
  intro r X e u hL hX hprod
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 1 ≤ (1+Real.log (L r))^a :=
    one_le_pow₀ (by linarith [Real.log_nonneg hL])
  have hcoef : E ≤ (E+1)^2 := by nlinarith
  have hpow : ((L r)^(5/6:ℝ))^2 = (L r)^(5/3:ℝ) := by
    rw [←Real.rpow_natCast ((L r)^(5/6:ℝ)) 2,←Real.rpow_mul hLp.le]
    norm_num
  have hlog : (1+Real.log (L r))^a ≤ ((1+Real.log (L r))^a)^2 := by nlinarith
  apply (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ E*(L r)^(5/3:ℝ)*(1+Real.log (L r))^a := henergy r X e u hL hX hprod
    _ = (L r)^(5/3:ℝ)*(E*(1+Real.log (L r))^a) := by ring
    _ ≤ (L r)^(5/3:ℝ)*((E+1)^2*((1+Real.log (L r))^a)^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hcoef hlog (by positivity) (sq_nonneg _)) (by positivity)
    _ = ((E+1)*(L r)^(5/6:ℝ)*(1+Real.log (L r))^a)^2 := by
      rw [mul_pow,mul_pow,hpow]
      ring

end CubicFirstMoment

end

end OAI
