import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstReduction
import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstStopping

namespace OAI

/-! The radial central kernel reduced to the two actual stopped branches.
The no-stop term is removed using one arbitrarily small fixed mesh for
all arities and all first-stage boundary choices. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_scaleFirstLow_sub_stopped_isLittleO (m : ℕ)
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    (ξ : ℝ) (Ct : ℕ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ ∀ (H : ℝ → ℝ),
      (∀ᶠ X : ℝ in atTop, 0 < H X) → ∀ h : ℝ → ℕ,
      (fun X => scaleFirstLowAritySum m ℓ ξ Ct (H X) X -
        (angular_scaleFirstStoppedSum ℓ m ρ ξ Ct (H X) X (h X) true +
          angular_scaleFirstStoppedSum ℓ m ρ ξ Ct (H X) X (h X) false))
        =o[atTop] firstMomentScale := by
  obtain ⟨ρ,hρ,hρ₂,hsmall,hn⟩ :=
    angular_distinguishedScaleNoStop_finite_isLittleO ℓ m hVor hGamma ξ Ct hcap
  refine ⟨ρ,hρ,hρ₂,hsmall,?_⟩
  intro H hH h
  have hsum := Asymptotics.IsLittleO.fun_sum (s := Finset.range m)
    (fun i hi => hn i (Finset.mem_range.mp hi) H
      (fun X => stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X)
        (X^(9/25:ℝ)) (h X)) hH)
  apply hsum.congr' ?_ Filter.EventuallyEq.rfl
  have hid : ∀ᶠ X : ℝ in atTop, ∀ i ∈ Finset.range m,
      ∀ (H : ℝ) (h : ℕ), distinguishedLowScaleRows i ℓ ξ Ct H X =
        angular_distinguishedScaleNoStop ℓ i ρ ξ Ct H X
          (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h) +
        angular_distinguishedScaleStopped ℓ i ρ ξ Ct H X h true +
        angular_distinguishedScaleStopped ℓ i ρ ξ Ct H X h false := by
    rw [Filter.eventually_all_finset]
    intro i _
    filter_upwards [angular_distinguishedLowScaleRows_two_stage ℓ i ξ] with X hX
    exact fun H h => hX ρ hρ hρ₂ Ct H h
  filter_upwards [hid] with X hid
  unfold scaleFirstLowAritySum angular_scaleFirstStoppedSum
  have he : (∑ i ∈ Finset.range m, distinguishedLowScaleRows i ℓ ξ Ct (H X) X) =
      ∑ i ∈ Finset.range m,
        (angular_distinguishedScaleNoStop ℓ i ρ ξ Ct (H X) X
          (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) (h X)) +
        angular_distinguishedScaleStopped ℓ i ρ ξ Ct (H X) X (h X) true +
        angular_distinguishedScaleStopped ℓ i ρ ξ Ct (H X) X (h X) false) :=
    Finset.sum_congr rfl (fun i hi => hid i hi (H X) (h X))
  rw [he,Finset.sum_add_distrib,Finset.sum_add_distrib]
  ring

end CubicFirstMoment

end

end OAI
