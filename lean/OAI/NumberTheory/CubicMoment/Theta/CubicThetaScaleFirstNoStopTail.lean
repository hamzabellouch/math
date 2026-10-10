import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstNoStopTail
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRestrictedNoStopWindow

namespace OAI

/-! The actual theta transform supplies the angular no-stop estimate.
No metaplectic Voronoi premise is used. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_scaleFirstTailNoStopRow_finite_bound_proved (ℓ : ℤ) (hℓ : ℓ ≠ 0) (m : ℕ) (hpnt : PrimaryPrimePNT)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {cap : ℝ} (hcap : 1 < cap) (M : ℕ) :
    ∃ ρ C E : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ 0 ≤ C ∧ 0 ≤ E ∧
      ∀ᶠ X : ℝ in atTop, ∀ i < m, ∀ (ξ H U : ℝ) (h : ℕ)
        (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
        0 < H → Real.log X ≤ U → U ≤ X^(1/100:ℝ) →
        ‖scaleFirstTailNoStopRow i ℓ ρ ξ H U X h d‖ ≤
          (1+Real.log X)*(C*X^(5/6-3/1600:ℝ)+E*X^(5/6:ℝ)/(Real.log X)^M) := by
  let A : ℝ := ∑ i ∈ Finset.range m, ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ)
  obtain ⟨ρ,C,hρ,hρ₂,hsmall,hC,hbound⟩ := angular_restricted_noStop_window_proved
    hpnt primeProductWeights hMV hMV0 ℓ hℓ
    (κ := (1/100:ℝ)) (η := 0) (ν := (1/100:ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (A := A) (by dsimp [A]; positivity) hcap
  refine ⟨ρ,C,0,hρ,hρ₂,hsmall,hC,le_rfl,?_⟩
  filter_upwards [hbound,eventually_ordinary_noStop_window_scales primeProductWeights,
    eventually_ge_atTop (max 2 (Real.exp (primeProductWeights.radius+Real.log 2))),
    Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with X hb hs hX hlog
  intro i hi ξ H U h d hH hLU hU
  have hAi : ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ) ≤ A := by
    dsimp only [A]
    exact Finset.single_le_sum (f := fun j : ℕ => ‖(j.factorial:ℂ)⁻¹‖*(j^j:ℕ))
      (fun j _ => by positivity) (Finset.mem_range.mpr hi)
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXp : 0 < X := by linarith
  have hUsq : U ≤ X^2 := hU.trans (by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ X by linarith) (show (1/100:ℝ) ≤ 2 by norm_num))
  have hlogs : 1+Real.log (X^(39/100:ℝ)) ≤ 1+Real.log X := by
    rw [Real.log_rpow hXp]
    linarith
  rw [scaleFirstTailNoStopRow_eq_window]
  have he := hb () (centralPrimaryFactors X) (distinguishedScaleCoefficient i ξ X d)
    primeDetectorCutoff (X^ξ) (X^(38/100:ℝ)) (X^(39/100:ℝ)) H U X
    (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h)
    hX hUsq hlog hs.1 hLU hH hXp hs.2.1 (Or.inl ⟨hs.2.2,hU⟩)
    (fun _ hr => (mem_primaryElementBall.mp hr).1)
    (fun r _ => (distinguishedScaleCoefficient_norm i ξ X d r).trans hAi)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
  convert he.trans (mul_le_mul_of_nonneg_right hlogs (by positivity)) using 1
  norm_num

end CubicFirstMoment

end

end OAI
