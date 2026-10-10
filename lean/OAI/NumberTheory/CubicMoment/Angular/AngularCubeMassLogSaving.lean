import OAI.NumberTheory.CubicMoment.Estimates.CubeMassLogSaving
import OAI.NumberTheory.CubicMoment.Angular.AngularDispersionModelEnergy
import OAI.NumberTheory.CubicMoment.Estimates.CubeMassComparison
import OAI.NumberTheory.CubicMoment.Estimates.DispersionModelEnergy
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! The cube variance model equals the true squarefree model mass with
arbitrary logarithmic accuracy. The truncation is a genuine log power. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_cube_mass_fullPrime_log_saving {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R : ℝ} (hR : 1 ≤ R) (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hVpos : tsupport V ⊆ Set.Ioi 0)
    (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ (b : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ r X e u A,
      T₀ ≤ L r → 1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      (L r)^(1/2:ℝ) ≤ A →
      ‖(finiteSieveDensity (squarefreeDivisorTruncation ((1+Real.log (L r))^b)):ℂ)*
          cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
            (angularHeightPrimeCoefficient ℓ R (W r) X) u V A-
        ((cStar^2*‖dispersionModel (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u‖^2:ℝ):ℂ)*squarefreeModelMass V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  let hv : UniformLogWeights (fun _ : Unit => V) := uniformLogWeights_constant V hV hVpos hV'
  obtain ⟨C,hC,hbound⟩ := hv.cubeModelTerm_mass_error
  obtain ⟨E,a,hE,henergy⟩ := angular_logarithmic_dispersionModel_energy ℓ hW hR hlo hhi
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp
    (negative_power_log_saving (show (0:ℝ) < 1/8 by norm_num) (a+k))
  refine ⟨2*(a+k),2*C*E+1,T₀,by positivity,?_⟩
  intro r X e u A hT₀ hL hX hprod hA
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hA1 : 1 ≤ A := (Real.one_le_rpow hL (by norm_num : (0:ℝ) ≤ 1/2)).trans hA
  have hz1 : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hs := squarefree_mass_log_scale hL hA a k (hT (L r) hT₀)
  have hb := hbound () (fullSquarefreePrimeSupport R (W r) X e)
    (angularHeightPrimeCoefficient ℓ R (W r) X) u A ((1+Real.log (L r))^(2*(a+k)))
    hA1 (one_le_pow₀ hz1)
  have he := henergy r X e u hL hX hprod
  apply (hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he hC.le) (by positivity))).trans
  calc
    _ = C*E*(L r)^(5/3:ℝ)*((1+Real.log (L r))^a*(A^(5/12:ℝ)+
        A^(2/3:ℝ)*((1+Real.log (L r))^(2*(a+k)))^(-(1/2:ℝ)))) := by ring
    _ ≤ C*E*(L r)^(5/3:ℝ)*(2*A^(2/3:ℝ)/(1+Real.log (L r))^k) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (2*C*E+1)*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
      have hh : 0 ≤ A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by positivity
      calc
        _ = (2*C*E)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by ring
        _ ≤ (2*C*E+1)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) :=
          mul_le_mul_of_nonneg_right (by linarith) hh
        _ = _ := by ring

end CubicFirstMoment

end

end OAI
