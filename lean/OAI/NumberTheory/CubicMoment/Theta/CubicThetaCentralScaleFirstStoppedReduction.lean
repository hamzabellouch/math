import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedReduction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralRestrictedNoStopParameters
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralScaleFirstReduction

namespace OAI

/-! The radial central kernel reduced to the two actual stopped branches.
The no-stop term is removed using one arbitrarily small fixed mesh for
all arities and all first-stage boundary choices. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment


theorem scaleFirstLow_sub_stopped_isLittleO_actual (m : ℕ)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (ξ : ℝ) (Ct : ℕ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ ∀ (H : ℝ → ℝ),
      (∀ᶠ X : ℝ in atTop, 0 < H X) → ∀ h : ℝ → ℕ,
      (fun X => scaleFirstLowAritySum m 0 ξ Ct (H X) X -
        (scaleFirstStoppedSum m ρ ξ Ct (H X) X (h X) true +
          scaleFirstStoppedSum m ρ ξ Ct (H X) X (h X) false))
        =o[atTop] firstMomentScale := by
  obtain ⟨ρ,hρ,hρ₂,hsmall,hn⟩ :=
    distinguishedScaleNoStop_finite_isLittleO_actual m  hGamma ξ Ct hcap
  refine ⟨ρ,hρ,hρ₂,hsmall,?_⟩
  intro H hH h
  have hsum := Asymptotics.IsLittleO.fun_sum (s := Finset.range m)
    (fun i hi => hn i (Finset.mem_range.mp hi) H
      (fun X => stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X)
        (X^(9/25:ℝ)) (h X)) hH)
  apply hsum.congr' ?_ Filter.EventuallyEq.rfl
  have hid : ∀ᶠ X : ℝ in atTop, ∀ i ∈ Finset.range m,
      ∀ (H : ℝ) (h : ℕ), distinguishedLowScaleRows i 0 ξ Ct H X =
        distinguishedScaleNoStop i ρ ξ Ct H X
          (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h) +
        distinguishedScaleStopped i ρ ξ Ct H X h true +
        distinguishedScaleStopped i ρ ξ Ct H X h false := by
    rw [Filter.eventually_all_finset]
    intro i _
    filter_upwards [distinguishedLowScaleRows_two_stage i ξ] with X hX
    exact fun H h => hX ρ hρ hρ₂ Ct H h
  filter_upwards [hid] with X hid
  unfold scaleFirstLowAritySum scaleFirstStoppedSum
  have he : (∑ i ∈ Finset.range m, distinguishedLowScaleRows i 0 ξ Ct (H X) X) =
      ∑ i ∈ Finset.range m,
        (distinguishedScaleNoStop i ρ ξ Ct (H X) X
          (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) (h X)) +
        distinguishedScaleStopped i ρ ξ Ct (H X) X (h X) true +
        distinguishedScaleStopped i ρ ξ Ct (H X) X (h X) false) :=
    Finset.sum_congr rfl (fun i hi => hid i hi (H X) (h X))
  rw [he,Finset.sum_add_distrib,Finset.sum_add_distrib]
  ring

theorem primeProductLowHeight_sub_stopped_isLittleO_actual
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ (m : ℕ) (ρ : ℝ), 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧
      ∀ (H : ℝ → ℝ), (∀ᶠ X : ℝ in atTop, 0 < H X) → ∀ h : ℝ → ℕ,
      (fun X => primeProductLowHeight 0 (H X) ((1+Real.log X)^Ct) X -
        (scaleFirstStoppedSum m ρ ξ Ct (H X) X (h X) true +
          scaleFirstStoppedSum m ρ ξ Ct (H X) X (h X) false))
        =o[atTop] firstMomentScale := by
  obtain ⟨m,hm⟩ := primeProductLowHeight_sub_low_scale_isLittleO_actual hpnt hSW hpub hHuxley hperiod
    hMV hC hξ hξz hGI hGQ  hGamma Ct
  obtain ⟨ρ,hρ,hρ₂,hsmall,hr⟩ := scaleFirstLow_sub_stopped_isLittleO_actual m  hGamma ξ Ct hcap
  refine ⟨m,ρ,hρ,hρ₂,hsmall,?_⟩
  intro H hH h
  apply ((hm H hH).add (hr H hH h)).congr' ?_ Filter.EventuallyEq.rfl
  exact Filter.Eventually.of_forall (fun X => by dsimp; ring)

end CubicFirstMoment

end

end OAI
