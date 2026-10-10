import OAI.NumberTheory.CubicMoment.Estimates.DivisorLogTail
import OAI.NumberTheory.CubicMoment.Estimates.DivisorTailScale
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! A small square divisor preserves the positive-power separation
between the high-frequency cutoff and its actual Poisson scale. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem divisor_high_poisson_log_saving {R η : ℝ}
    (hR : 1 ≤ R) (hη : 0 < η) (hη₁ : η ≤ 1)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ),
      T₀ ≤ L r → 1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ∀ (A : ℝ) (d e : Eisenstein) (u : ℝ) (n : ℕ) (H : ℕ → Finset Eisenstein)
      (hd : d ≠ 0), norm d ≤ (L r)^(η/16) →
      (L r)^(1-η/16) ≤ A → A ≤ (L r)^2 →
      (L r)^(1+η/2) ≤ (2:ℝ)^n → (∀ j, H j ⊆ divisorFrequencyDyad d hd j) →
      Summable (fun j => finiteDivisorPoissonContribution d (fullSquarefreePrimeSupport R (W r) X e)
        (H (j+n)) (fullPrimeCoefficient R (W r) X) u V A) ∧
      ‖∑' j : ℕ, finiteDivisorPoissonContribution d (fullSquarefreePrimeSupport R (W r) X e)
        (H (j+n)) (fullPrimeCoefficient R (W r) X) u V A‖ ≤ K/(1+Real.log (L r))^k := by
  obtain ⟨m,hm⟩ := exists_nat_gt (44/η)
  have hm' : 11 ≤ (η/4)*(m:ℝ) := by
    have hh := (div_lt_iff₀ hη).mp hm
    nlinarith
  obtain ⟨K,a,hK,hbound⟩ := logarithmic_divisor_poisson_tail hR hW hlo hhi V hV hV' m
  let D := 27*(R^Fintype.card ι)^2
  have hD : 0 < D := by dsimp [D]; positivity
  let C := 2*K*D^(m+3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp
    (negative_power_log_saving (by norm_num : (0:ℝ) < 2) (a+k))
  refine ⟨C+1,T₀,by positivity,?_⟩
  intro r X hT₀ hL hX hprod A d e u n H hd hdhi hAlo hAhi hcut hH
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  have hd1 : 1 ≤ norm d := one_le_norm hd
  have hA : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  let t := A/(D*(norm d)^3*(L r)^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have heq : A/(27*(norm d)^3*(R^Fintype.card ι*L r)^2) = t := by dsimp [t,D]; ring
  have hb := hbound r X hL hX hprod A d e u n H hd hA hH
  dsimp only at hb
  rw [heq] at hb
  refine ⟨hb.1,?_⟩
  have hAlo' := divisor_tail_lower_scale hL hdN.le hdhi hAlo hdN
  have hscale := poisson_cutoff_scale hL hη₁ hAlo' hcut hD
  have heq' : (A/(norm d)^3)/(D*(L r)^2) = t := by dsimp [t]; ring
  rw [heq'] at hscale
  have hp := poisson_tail_power_gap hL (div_nonneg hA.le (sq_nonneg _))
    (divisor_tail_upper_scale hA.le hd1 hAhi) ht (by positivity : 0 < (2:ℝ)^n)
    hD hscale.1 hscale.2 m hm'
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hgeo : ((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹ ≤ 2 := by
    norm_num
    have hh : (1/4:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hlog : (1+Real.log (L r))^a*(L r)^(-2:ℝ) ≤ 1/(1+Real.log (L r))^k := by
    apply (mul_le_mul_of_nonneg_left (hT (L r) hT₀) (pow_nonneg hz.le a)).trans_eq
    rw [pow_add]
    field_simp
  calc
    _ ≤ (K*(A/(norm d)^2)*L r*(1+Real.log (L r))^a/(t*(2:ℝ)^n)^m)*
        (t^(-3:ℝ)*2) := hb.2.trans (mul_le_mul_of_nonneg_left
          (by nlinarith [mul_le_mul_of_nonneg_left hgeo (Real.rpow_nonneg ht.le (-3))]) (by positivity))
    _ = (2*K*(1+Real.log (L r))^a)*((A/(norm d)^2)*L r*t^(-3:ℝ)/(t*(2:ℝ)^n)^m) := by ring
    _ ≤ (2*K*(1+Real.log (L r))^a)*(D^(m+3)*(L r)^(-2:ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = C*((1+Real.log (L r))^a*(L r)^(-2:ℝ)) := by dsimp [C]; ring
    _ ≤ C*(1/(1+Real.log (L r))^k) := mul_le_mul_of_nonneg_left hlog hC
    _ ≤ _ := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end CubicFirstMoment

end

end OAI
