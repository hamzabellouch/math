import OAI.NumberTheory.CubicMoment.Estimates.ProfilePoissonEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.SmallBUnboundedTail

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment.ProfileControl

theorem smallB_poisson_tail_power_unbounded :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (A N Z u : ℝ) (n : ℕ),
      1 ≤ N → N ≤ Z → Z^(3/2:ℝ) ≤ A → Z^(3/4:ℝ)/32 ≤ (2:ℝ)^n →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) →
      (∀ j, H j ⊆ frequencyDyad j) →
      Summable (fun j => finitePoissonContribution S (H (j+n)) β u P.V A) ∧
      ‖∑' j : ℕ, finitePoissonContribution S (H (j+n)) β u P.V A‖ ≤
        (K*P.cost)*Z^(-2:ℝ)*∑ a ∈ S, ‖β a‖^2 := by
  obtain ⟨K₀,hK₀,hbound₀⟩ := arbitrary_poisson_energy_tail 44 (by norm_num)
  refine ⟨2*K₀*(864:ℝ)^47,by positivity,?_⟩
  intro P S H β A N Z u n hN hNZ hAlo hcut hS hH
  let K := K₀*P.cost
  have hK : 0 < K := mul_pos hK₀ P.cost_pos
  have hbound := hbound₀ P
  have hZ : 1 ≤ Z := hN.trans hNZ
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hA : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hAlo
  let t := A/(27*Z^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hb := hbound S H β A N Z u n hA hNp hNZ hS hH
  refine ⟨hb.1,?_⟩
  have hp := smallB_unbounded_tail_scale hZ hAlo hcut
  have hgeo : ((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹ ≤ 2 := by
    norm_num
    have hh : (1/4:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  calc
    _ ≤ (K*(A/N)*Z*(∑ a ∈ S, ‖β a‖^2)/(t*(2:ℝ)^n)^44)*(t^(-3:ℝ)*2) :=
      hb.2.trans (mul_le_mul_of_nonneg_left
        (by nlinarith [mul_le_mul_of_nonneg_left hgeo (Real.rpow_nonneg ht.le (-3))])
        (by positivity))
    _ = (2*K/N)*(∑ a ∈ S, ‖β a‖^2)*(A*Z*t^(-3:ℝ)/(t*(2:ℝ)^n)^44) := by ring
    _ ≤ (2*K/N)*(∑ a ∈ S, ‖β a‖^2)*((864:ℝ)^47*Z^(-2:ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (2*K)*(∑ a ∈ S, ‖β a‖^2)*((864:ℝ)^47*Z^(-2:ℝ)) := by
      gcongr
      exact div_le_self (by positivity) hN
    _ = _ := by dsimp [K]; ring

end CubicFirstMoment.ProfileControl

end

end OAI
