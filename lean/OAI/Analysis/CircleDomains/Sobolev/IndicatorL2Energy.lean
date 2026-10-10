import OAI.Analysis.CircleDomains.Sobolev.SphericalGradientEnergyNorm

namespace OAI

/-! Convert a small weighted mass of a changed set into the exact L2
error contribution used by source priority interpolation. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem indicator_L2_norm_lt_of_energy_lt
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {g : X → ℝ}
    (hg : MemLp g 2 μ) {S : Set X} (hS : MeasurableSet S)
    {τ : ℝ} (hτ : 0 < τ)
    (hE : (∫⁻ x in S, ENNReal.ofReal (g x^2) ∂μ) < ENNReal.ofReal (τ^2)) :
    (eLpNorm (S.indicator g) 2 μ).toReal < τ := by
  have hi := (hg.restrict S).integrable_sq
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun x => sq_nonneg (g x)))
  rw [← he] at hE
  have hb : (∫ x in S, g x^2 ∂μ) < τ^2 := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hE
  have hp : (fun x => (S.indicator g x)^2) = S.indicator (fun x => g x^2) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, zero_pow (by decide : 2 ≠ 0)]
  have hn := integral_sq_eq_eLpNorm_toReal_sq (hg.indicator hS)
  rw [hp, integral_indicator hS] at hn
  rw [hn] at hb
  nlinarith [ENNReal.toReal_nonneg (a := eLpNorm (S.indicator g) 2 μ)]

end CircleDomainRigidity

end

end OAI
