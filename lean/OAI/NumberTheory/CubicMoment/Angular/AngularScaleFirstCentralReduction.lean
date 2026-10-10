import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstReduction
import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstStoppedReduction

namespace OAI

noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_primeProductLowHeight_sub_stopped_isLittleO
    (hpnt : PrimaryPrimePNT) (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (hGammaℓ : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    (Ct : ℕ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ (m : ℕ) (ρ : ℝ), 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧
      ∀ (H : ℝ → ℝ), (∀ᶠ X : ℝ in atTop, 0 < H X) → ∀ h : ℝ → ℕ,
      (fun X => primeProductLowHeight ℓ (H X) ((1+Real.log X)^Ct) X -
        (angular_scaleFirstStoppedSum ℓ m ρ ξ Ct (H X) X (h X) true +
          angular_scaleFirstStoppedSum ℓ m ρ ξ Ct (H X) X (h X) false))
        =o[atTop] firstMomentScale := by
  obtain ⟨m,hm⟩ := angular_primeProductLowHeight_sub_low_scale_isLittleO ℓ hpnt hSW hℓ hpub hHuxley hperiod
    hMV hC hξ hξz hGI hGQ hVor hGamma Ct
  obtain ⟨ρ,hρ,hρ₂,hsmall,hr⟩ := angular_scaleFirstLow_sub_stopped_isLittleO ℓ m hVor hGammaℓ ξ Ct hcap
  refine ⟨m,ρ,hρ,hρ₂,hsmall,?_⟩
  intro H hH h
  apply ((hm H hH).add (hr H hH h)).congr' ?_ Filter.EventuallyEq.rfl
  exact Filter.Eventually.of_forall (fun X => by dsimp; ring)


end CubicFirstMoment

end

end OAI
