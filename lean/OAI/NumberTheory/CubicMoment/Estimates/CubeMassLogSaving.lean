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

lemma squarefree_mass_log_scale {L A : ℝ} (hL : 1 ≤ L) (hA : L^(1/2:ℝ) ≤ A)
    (a k : ℕ) (hlog : L^(-(1/8:ℝ)) ≤ 1/(1+Real.log L)^(a+k)) :
    (1+Real.log L)^a*(A^(5/12:ℝ)+
      A^(2/3:ℝ)*((1+Real.log L)^(2*(a+k)))^(-(1/2:ℝ))) ≤
      2*A^(2/3:ℝ)/(1+Real.log L)^k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hAp : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hA
  have hz : 0 < 1+Real.log L := by linarith [Real.log_nonneg hL]
  have hp : A^(5/12:ℝ) = A^(2/3:ℝ)*A^(-(1/4:ℝ)) := by
    rw [←Real.rpow_add hAp]
    norm_num
  have hdecay : A^(-(1/4:ℝ)) ≤ L^(-(1/8:ℝ)) := by
    calc
      _ ≤ (L^(1/2:ℝ))^(-(1/4:ℝ)) := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hLp _) hA (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hLp.le]; norm_num
  have hzpow : ((1+Real.log L)^(2*(a+k)))^(-(1/2:ℝ)) =
      1/(1+Real.log L)^(a+k) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
    have he : (↑(2*(a+k)):ℝ)*(-(1/2:ℝ)) = -(↑(a+k):ℝ) := by push_cast; ring
    rw [he,Real.rpow_neg hz.le,Real.rpow_natCast,one_div]
  have hc : (1+Real.log L)^a*(1/(1+Real.log L)^(a+k)) =
      1/(1+Real.log L)^k := by
    rw [pow_add]
    field_simp
  rw [hp,hzpow]
  calc
    _ ≤ (1+Real.log L)^a*(A^(2/3:ℝ)*(1/(1+Real.log L)^(a+k))+
        A^(2/3:ℝ)*(1/(1+Real.log L)^(a+k))) := by
      gcongr
      exact hdecay.trans hlog
    _ = 2*A^(2/3:ℝ)*((1+Real.log L)^a*(1/(1+Real.log L)^(a+k))) := by ring
    _ = _ := by rw [hc]; ring

theorem cube_mass_fullPrime_log_saving {γ ι : Type*} [Fintype ι] [DecidableEq ι]
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
            (fullPrimeCoefficient R (W r) X) u V A-
        ((cStar^2*‖dispersionModel (fullSquarefreePrimeSupport R (W r) X e)
          (fullPrimeCoefficient R (W r) X) u‖^2:ℝ):ℂ)*squarefreeModelMass V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  let hv : UniformLogWeights (fun _ : Unit => V) := uniformLogWeights_constant V hV hVpos hV'
  obtain ⟨C,hC,hbound⟩ := hv.cubeModelTerm_mass_error
  obtain ⟨E,a,hE,henergy⟩ := logarithmic_dispersionModel_energy hW hR hlo hhi
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp
    (negative_power_log_saving (show (0:ℝ) < 1/8 by norm_num) (a+k))
  refine ⟨2*(a+k),2*C*E+1,T₀,by positivity,?_⟩
  intro r X e u A hT₀ hL hX hprod hA
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hA1 : 1 ≤ A := (Real.one_le_rpow hL (by norm_num : (0:ℝ) ≤ 1/2)).trans hA
  have hz1 : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hs := squarefree_mass_log_scale hL hA a k (hT (L r) hT₀)
  have hb := hbound () (fullSquarefreePrimeSupport R (W r) X e)
    (fullPrimeCoefficient R (W r) X) u A ((1+Real.log (L r))^(2*(a+k)))
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
