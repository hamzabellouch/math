import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstStoppedLate
import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstStoppedAggregation
import OAI.NumberTheory.CubicMoment.Estimates.LogPowerSaving

namespace OAI

/-! Every finite collection of actual late stopped arities is negligible;
the powers of logarithms from every finite partition are absorbed. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_scaleFirstStoppedLate_isLittleO (ℓ : ℤ) (m : ℕ) (hpnt : PrimaryPrimePNT)
    {C ξ ρ ε : ℝ} (hC : 0 < C) (hξ : 0 < ξ)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    (hgap : ξ+ε < 1/100) (Ct : ℕ) (H : ℝ → ℝ) (h : ℝ → ℕ)
    (hH : ∀ᶠ X : ℝ in atTop, 0 < H X)
    (hh : ∀ᶠ X : ℝ in atTop,
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h X)
    (hboundary : ∀ᶠ X : ℝ in atTop,
      ρ*geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X) ≤ (Real.log X)^C) :
    (fun X => angular_scaleFirstStoppedSum ℓ m ρ ξ Ct (H X) X (h X) false)
      =o[atTop] firstMomentScale := by
  unfold angular_scaleFirstStoppedSum
  apply Asymptotics.IsLittleO.fun_sum
  intro i _hi
  obtain ⟨τ,K,hτ,hK,hbound⟩ := angular_distinguishedStoppedLate_bound ℓ i hpnt hC hξ
    hρ hρ₂ hε hsmall hgap Ct
  obtain ⟨D,hD,hagg⟩ := angular_distinguishedScaleStopped_bound ℓ i hρ
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => (1+Real.log X)^(i+5+Ct)*X^(5/6-τ)) ?_
    (log_power_powerSaving_isLittleO (i+5+Ct) hτ)
  apply Asymptotics.IsBigO.of_bound (D*K)
  filter_upwards [hbound,hH,hh,hboundary,eventually_ge_atTop (1:ℝ)]
    with X hbound hH hh hboundary hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hpiece (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
      (q : ℕ × ℕ × ℕ)
      (hq : q ∈ (if false then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
        (fun q => q.1 < h X) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)))
      (j r : ℕ) :
      ‖angular_distinguishedStoppedDyad ℓ i ρ ξ Ct (H X) X (h X) false d q j r‖ ≤
        K*(1+Real.log X)^Ct*X^(5/6-τ) := by
    have hk : 1 ≤ q.2.1 := (Finset.mem_filter.mp hq).2
    exact hbound (H X) hH (h X) hh hboundary d q j r hk
  have hs := hagg Ct ξ (H X) X hX (h X) false
    (K*(1+Real.log X)^Ct*X^(5/6-τ)) (by positivity) hpiece
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ (1+Real.log X)^(i+5+Ct)*X^(5/6-τ))]
  apply hs.trans_eq
  rw [pow_add]
  ring

end CubicFirstMoment

end

end OAI
