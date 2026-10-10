import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstHighSum
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralLargeTupleHighSum
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralScaleFirstMiddleSum

namespace OAI

/-! The high-scale branch is negligible. The middle interval is treated
by its distinguished group; the higher interval is the large-row high sum. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem scaleFirstHighSum_isLittleO_actual (i j : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => scaleFirstHighSum i j ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  have hh := largePrimeTupleHighSum_isLittleO_actual i j hpnt hSW hpub hHuxley hperiod hMV hC
    hξ hξz (by norm_num : (0:ℝ) < 1/100) (by norm_num : (1/100:ℝ) ≤ 1/12)
    hGI hGQ  hGamma Ct H hH
  have hm := scaleFirstMiddleSum_isLittleO_actual i j hSW hpub hHuxley hperiod hMV hC
    hξ hξz hGI hGQ  hGamma Ct H hH
  apply (hh.add hm).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
  exact (scaleFirstHighSum_split i j ξ Ct (H X) hX).symm

end CubicFirstMoment

end

end OAI
