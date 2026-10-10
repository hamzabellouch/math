import OAI.NumberTheory.CubicMoment.Estimates.CommonOuterPowers
import OAI.NumberTheory.CubicMoment.Estimates.CubeErrorPowers
import OAI.NumberTheory.CubicMoment.Estimates.LogCoefficientEnergy
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! The actual noncoprime part of the small-divisor variance is
logarithmically negligible. No new analytic input is assumed here. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fullPrime_divisor_noncoprime_log_saving {R c η : ℝ} (hR : 1 ≤ R)
    (hc : 0 < c) (hc1 : c ≤ 1) (hηc : η ≤ c)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ (G : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (d e : Eisenstein) (u : ℝ), T₀ ≤ L r → 1 ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → (∀ i, (L r)^c < X i) →
      primary d → norm d ≤ L r → (L r)^(1-η) ≤ A →
      A ≤ (L r)^2/(1+Real.log (L r))^G →
      ‖divisorDispersionVariance d (fullSquarefreePrimeSupport R (W r) X e)
          (fullPrimeCoefficient R (W r) X) u V A-
        divisorCoprimeDispersionGram d (fullSquarefreePrimeSupport R (W r) X e)
          (fullPrimeCoefficient R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,hC,hbound⟩ := fullPrime_divisor_noncoprime_outer (ι := ι)
    (show 0 < c/100 by positivity) (show c/100 ≤ 1 by linarith) hR V hV hV'
  obtain ⟨E,a,hE,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp
    (negative_power_log_saving (show 0 < c/4 by positivity) (a+k))
  let B := R^Fintype.card ι
  let F := (2:ℝ)^(3*Fintype.card ι)
  let K₀ := ‖normProfileFourier V 0‖/9
  let K₁ := K₀*F*(E+1)+3*C*B^(c/100)*F*(E+1)+1
  refine ⟨3*(a+k),K₁,T₀,by dsimp [K₁,K₀,F,B]; positivity,?_⟩
  intro r X A d e u hT₀ hL hX hprod hrough hd hdL hAlo hAhi
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hA : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hz1 : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hz : 0 < 1+Real.log (L r) := zero_lt_one.trans_le hz1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hh := hbound (W r) X (L r) ((L r)^c) A e d
    (fullPrimeCoefficient R (W r) X) u (fun i => zero_lt_one.trans_le (hX i)) hprod hL
    (Real.one_le_rpow hL hc.le) hA hd (hlo r) (hhi r) hrough
  have hcost := commonOuterCost_power_saving V hC.le hB (norm_nonneg d) hdL
    hL hA hc hc1 hηc hAlo
  have he : (∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
      ‖fullPrimeCoefficient R (W r) X b‖^2) ≤ (E+1)*L r*(1+Real.log (L r))^a := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans
    apply (henergy r X hL hX hprod).trans
    nlinarith [mul_nonneg hLp.le (pow_nonneg hz.le a)]
  have hlattice := cube_lattice_error_scale hA hLp hz a k hAhi
  have hlog : (1+Real.log (L r))^a*(L r)^(-c/4) ≤ 1/(1+Real.log (L r))^k := by
    rw [show -c/4 = -(c/4) by ring]
    apply (mul_le_mul_of_nonneg_left (hT (L r) hT₀) (pow_nonneg hz.le a)).trans_eq
    rw [pow_add]
    field_simp
  have hpower : (L r)^(2/3:ℝ)*L r = (L r)^(5/3:ℝ) := by
    calc
      _ = (L r)^(2/3:ℝ)*(L r)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hLp]; norm_num
  have hsplit : ((K₀*A+3*C*B^(c/100)*A^(2/3:ℝ)*(L r)^(2/3:ℝ)*(L r)^(-c/4))*F)*
      ((E+1)*L r*(1+Real.log (L r))^a) =
      (K₀*F*(E+1))*(A*L r*(1+Real.log (L r))^a)+
      (3*C*B^(c/100)*F*(E+1))*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*
        ((1+Real.log (L r))^a*(L r)^(-c/4)) := by
    rw [← hpower]
    ring
  apply (hh.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcost (by positivity))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans
    (mul_le_mul_of_nonneg_left he (by positivity)))).trans
  change ((K₀*A+3*C*B^(c/100)*A^(2/3:ℝ)*(L r)^(2/3:ℝ)*(L r)^(-c/4))*F)*
    ((E+1)*L r*(1+Real.log (L r))^a) ≤ _
  rw [hsplit]
  calc
    _ ≤ (K₀*F*(E+1))*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k)+
        (3*C*B^(c/100)*F*(E+1))*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*
          (1/(1+Real.log (L r))^k) := add_le_add
      (mul_le_mul_of_nonneg_left hlattice (by dsimp [K₀,F]; positivity))
      (mul_le_mul_of_nonneg_left hlog (by dsimp [F,B]; positivity))
    _ = (K₀*F*(E+1)+3*C*B^(c/100)*F*(E+1))*
        (A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by ring
    _ ≤ K₁*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [K₁]
      linarith
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
