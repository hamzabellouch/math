import OAI.NumberTheory.CubicMoment.Estimates.PrimeModelCutoff
import OAI.NumberTheory.CubicMoment.Estimates.HeightWindowCount
import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorPowers

namespace OAI

/-! The entire large-height part of the undecomposed prime model is
negligible at the first-moment scale, with the actual finite windows. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def primeModelWindowSum (P : Finset Eisenstein) (c : Eisenstein → ℂ) (ℓ : ℤ)
    (H T₀ X₀ : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (heightWindowCount H T₀),
    ∑ p ∈ P, (c p*theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ))*
      heightFourierIntegral
        (fun t => cutoffHeightMultiplier H t*heightWindow (T₀*(3/2:ℝ)^j) t)
        (Real.log (norm p)-Real.log X₀)

theorem prime_model_window_sum_bound {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Finset Eisenstein) (c : Eisenstein → ℂ)
      (ℓ : ℤ) (X X₀ T₀ H M δ : ℝ), 1 ≤ X → 0 < X₀ → 1 ≤ T₀ → 1 ≤ H →
      2*Real.pi*H ≤ X → X^δ ≤ T₀ → 0 ≤ M →
      (∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X) →
      (∀ p ∈ P, ‖c p‖ ≤ M) →
      ‖primeModelWindowSum P c ℓ H T₀ X₀‖ ≤
        K*M*(1+Real.log H)*X^(5/6-δ/2) := by
  obtain ⟨K,hK,hcount⟩ := heightWindowCount_log_bound
  refine ⟨4*K*(Real.sqrt (720*C)+1),by positivity,?_⟩
  intro P c ℓ X X₀ T₀ H M δ hX hX₀ hT₀ hH hcap hδ hM hP hc
  have hT : 0 < T₀ := zero_lt_one.trans_le hT₀
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hb (j : ℕ) (hj : j ∈ Finset.range (heightWindowCount H T₀)) :
      ‖∑ p ∈ P, (c p*theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ))*
        heightFourierIntegral
          (fun t => cutoffHeightMultiplier H t*heightWindow (T₀*(3/2:ℝ)^j) t)
          (Real.log (norm p)-Real.log X₀)‖ ≤
        4*Real.sqrt (720*C)*M*X^(5/6-δ/2) := by
    have hs := heightWindowCount_scale_bounds hH0 hT (Finset.mem_range.mp hj)
    exact prime_model_cutoff_power_saving hMV hC P c H hX hX₀
      (hs.2.le.trans hcap) (hδ.trans hs.1) hM hP hc ℓ
  unfold primeModelWindowSum
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ (heightWindowCount H T₀:ℝ)*(4*Real.sqrt (720*C)*M*X^(5/6-δ/2)) := by
      simpa using Finset.sum_le_sum hb
    _ ≤ (K*(1+Real.log H))*(4*Real.sqrt (720*C)*M*X^(5/6-δ/2)) :=
      mul_le_mul_of_nonneg_right (hcount H T₀ hH hT₀) (by positivity)
    _ ≤ _ := by
      have hl : 0 ≤ 1+Real.log H := by linarith [Real.log_nonneg hH]
      nlinarith [mul_nonneg (show 0 ≤ K*M*(1+Real.log H)*X^(5/6-δ/2) by positivity)
        (show (0:ℝ) ≤ 1 by norm_num)]

theorem prime_model_large_height_isLittleO {C M a δ : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (ha : 0 < a) (ha1 : a < 1) (hδ : 0 < δ)
    (P : ℝ → Finset Eisenstein) (c : ℝ → Eisenstein → ℂ) (ℓ : ℤ)
    (hP : ∀ X, 1 ≤ X → ∀ p ∈ P X, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ X, 1 ≤ X → ∀ p ∈ P X, ‖c X p‖ ≤ M) :
    (fun X : ℝ => primeModelWindowSum (P X) (c X) ℓ (X^a) (X^δ) X)
      =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := prime_model_window_sum_bound hMV hC
  obtain ⟨D,hD,hlog⟩ := one_add_log_small_power (show 0 < δ/4 by positivity)
  apply isLittleO_of_powerSaving (show 0 < δ/4 by positivity)
  apply Asymptotics.IsBigO.of_bound (K*M*D)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0 < 1-a by linarith)).eventually_ge_atTop (2*Real.pi)] with X hX hgrow
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hcap : 2*Real.pi*X^a ≤ X := by
    apply (mul_le_mul_of_nonneg_right hgrow (Real.rpow_nonneg hXp.le a)).trans_eq
    rw [← Real.rpow_add hXp]
    have he : 1-a+a = (1:ℝ) := by ring
    rw [he,Real.rpow_one]
  have hh := hbound (P X) (c X) ℓ X X (X^δ) (X^a) M δ hX hXp
    (Real.one_le_rpow hX hδ.le) (Real.one_le_rpow hX ha.le) hcap le_rfl hM
    (hP X hX) (hc X hX)
  have hlogs : 1+Real.log (X^a) ≤ D*X^(δ/4) := by
    rw [Real.log_rpow hXp]
    exact (show 1+a*Real.log X ≤ 1+Real.log X by
      nlinarith [Real.log_nonneg hX]).trans (hlog X hX)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hXp.le _)]
  apply hh.trans
  calc
    _ ≤ K*M*(D*X^(δ/4))*X^(5/6-δ/2) := by gcongr
    _ = (K*M*D)*(X^(δ/4)*X^(5/6-δ/2)) := by ring
    _ = K*M*D*X^(5/6-δ/4) := by
      rw [← Real.rpow_add hXp]
      congr 2
      ring

end CubicFirstMoment

end

end OAI
