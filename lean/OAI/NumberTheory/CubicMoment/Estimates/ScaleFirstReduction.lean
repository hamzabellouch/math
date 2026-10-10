import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstRowCollection
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeNegligible

namespace OAI

/-! The radial central comparison after the complete high-scale branch
has been discharged. Only the faithful low-scale stopping problem remains. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem distinguishedHighScaleRows_isLittleO (i : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => distinguishedHighScaleRows i 0 ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  obtain ⟨m,hm⟩ := distinguishedHighScaleRows_arity hξ
  have hb : (fun X => ∑ j ∈ Finset.range m, scaleFirstHighSum i j ξ Ct (H X) X)
      =o[atTop] firstMomentScale := by
    exact Asymptotics.IsLittleO.fun_sum (s := Finset.range m)
      (fun j _ => scaleFirstHighSum_isLittleO i j hpnt hSW hpub hHuxley hperiod hMV hC
        hξ hξz hGI hGQ hVor hGamma Ct H hH)
  apply hb.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hm] with X hm
  exact (hm i 0 Ct (H X)).symm

def scaleFirstLowAritySum (m : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ i ∈ Finset.range m, distinguishedLowScaleRows i ℓ ξ Ct H X

theorem centralRoughProduct_sub_low_scale_isLittleO
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) :
    ∃ m : ℕ, ∀ (H : ℝ → ℝ), (∀ᶠ X : ℝ in atTop, 0 < H X) →
      (fun X => centralRoughProduct 0 (H X) ((1+Real.log X)^Ct) X -
        scaleFirstLowAritySum m 0 ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  obtain ⟨m,hm⟩ := centralRoughProduct_by_distinguished_scale hξ hξz
  refine ⟨m,?_⟩
  intro H hH
  have hb : (fun X => ∑ i ∈ Finset.range m, distinguishedHighScaleRows i 0 ξ Ct (H X) X)
      =o[atTop] firstMomentScale := by
    exact Asymptotics.IsLittleO.fun_sum (s := Finset.range m)
      (fun i _ => distinguishedHighScaleRows_isLittleO i hpnt hSW hpub hHuxley hperiod hMV hC
        hξ hξz hGI hGQ hVor hGamma Ct H hH)
  apply hb.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hm] with X hm
  rw [hm 0 Ct (H X),Finset.sum_add_distrib]
  unfold scaleFirstLowAritySum
  ring

theorem primeProductLowHeight_sub_low_scale_isLittleO
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) :
    ∃ m : ℕ, ∀ (H : ℝ → ℝ), (∀ᶠ X : ℝ in atTop, 0 < H X) →
      (fun X => primeProductLowHeight 0 (H X) ((1+Real.log X)^Ct) X -
        scaleFirstLowAritySum m 0 ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  obtain ⟨m,hm⟩ := centralRoughProduct_sub_low_scale_isLittleO hpnt hSW hpub hHuxley hperiod
    hMV hC hξ hξz hGI hGQ hVor hGamma Ct
  refine ⟨m,?_⟩
  intro H hH
  have hs := centralSemiprimeProduct_isLittleO hSW hpub hHuxley hperiod hMV hC
    hGI hGQ hVor hGamma Ct H hH
  apply ((hm H hH).sub hs).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [primeProductLowHeight_detector 0] with X hX
  rw [hX (H X) ((1+Real.log X)^Ct)]
  ring

end CubicFirstMoment

end

end OAI
