import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstReduction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralAngularScaleFirstHighSum
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralAngularSemiprimeNegligible

namespace OAI

/-! The fixed-angular central comparison after the complete high-scale branch
has been discharged. Only the faithful low-scale stopping problem remains. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)


theorem angular_distinguishedHighScaleRows_isLittleO_actual (i : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => distinguishedHighScaleRows i ℓ ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  obtain ⟨m,hm⟩ := distinguishedHighScaleRows_arity hξ
  have hb : (fun X => ∑ j ∈ Finset.range m, angular_scaleFirstHighSum ℓ i j ξ Ct (H X) X)
      =o[atTop] firstMomentScale := by
    exact Asymptotics.IsLittleO.fun_sum (s := Finset.range m)
      (fun j _ => angular_scaleFirstHighSum_isLittleO_actual ℓ i j hpnt hSW hℓ hpub hHuxley hperiod hMV hC
        hξ hξz hGI hGQ  hGamma Ct H hH)
  apply hb.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hm] with X hm
  exact (hm i ℓ Ct (H X)).symm

theorem angular_centralRoughProduct_sub_low_scale_isLittleO_actual
    (hpnt : PrimaryPrimePNT) (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) :
    ∃ m : ℕ, ∀ (H : ℝ → ℝ), (∀ᶠ X : ℝ in atTop, 0 < H X) →
      (fun X => centralRoughProduct ℓ (H X) ((1+Real.log X)^Ct) X -
        scaleFirstLowAritySum m ℓ ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  obtain ⟨m,hm⟩ := centralRoughProduct_by_distinguished_scale hξ hξz
  refine ⟨m,?_⟩
  intro H hH
  have hb : (fun X => ∑ i ∈ Finset.range m, distinguishedHighScaleRows i ℓ ξ Ct (H X) X)
      =o[atTop] firstMomentScale := by
    exact Asymptotics.IsLittleO.fun_sum (s := Finset.range m)
      (fun i _ => angular_distinguishedHighScaleRows_isLittleO_actual ℓ i hpnt hSW hℓ hpub hHuxley hperiod hMV hC
        hξ hξz hGI hGQ  hGamma Ct H hH)
  apply hb.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hm] with X hm
  rw [hm ℓ Ct (H X),Finset.sum_add_distrib]
  unfold scaleFirstLowAritySum
  ring

theorem angular_primeProductLowHeight_sub_low_scale_isLittleO_actual
    (hpnt : PrimaryPrimePNT) (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) :
    ∃ m : ℕ, ∀ (H : ℝ → ℝ), (∀ᶠ X : ℝ in atTop, 0 < H X) →
      (fun X => primeProductLowHeight ℓ (H X) ((1+Real.log X)^Ct) X -
        scaleFirstLowAritySum m ℓ ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  obtain ⟨m,hm⟩ := angular_centralRoughProduct_sub_low_scale_isLittleO_actual ℓ hpnt hSW hℓ hpub hHuxley hperiod
    hMV hC hξ hξz hGI hGQ  hGamma Ct
  refine ⟨m,?_⟩
  intro H hH
  have hs := angular_centralSemiprimeProduct_isLittleO_actual ℓ hSW hℓ hpub hHuxley hperiod hMV hC
    hGI hGQ  hGamma Ct H hH
  apply ((hm H hH).sub hs).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [primeProductLowHeight_detector ℓ] with X hX
  rw [hX (H X) ((1+Real.log X)^Ct)]
  ring

end CubicFirstMoment

end

end OAI
