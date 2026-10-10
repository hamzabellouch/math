import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleHighSum
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralLargeTupleExceptionalHigh
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralLargeTupleOrdinarySum

namespace OAI

/-! All high boxes of each actual large-row arity are negligible. The
separate sharp-cutoff boundary contribution is retained explicitly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem largePrimeTupleHighSum_isLittleO_actual (i j : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) (hδ1 : δ ≤ 1/12)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => largePrimeTupleHighSum i j ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  have ho := largePrimeTupleOrdinaryHighSum_isLittleO_actual i j hSW hpub hHuxley hperiod
    hMV hC hξ hξz hδ hGI hGQ  hGamma Ct H hH
  have he : (fun X => largePrimeTupleExceptionalHighSum i j ξ δ Ct (H X) X)
      =o[atTop] firstMomentScale := by
    by_cases hij : i+j = 3
    · exact largePrimeTupleExceptionalHighSum_isLittleO_actual i j hij hpnt hSW hpub hHuxley
        hperiod hMV hC hξ hξz hδ1 hGI hGQ  hGamma Ct H hH
    · have hz : (fun X => largePrimeTupleExceptionalHighSum i j ξ δ Ct (H X) X) =
          fun _ : ℝ => (0:ℂ) := by
        funext X
        exact largePrimeTupleExceptionalHighSum_zero i j hij ξ δ Ct (H X) X
      rw [hz]
      exact Asymptotics.isLittleO_zero _ _
  have hs : (fun X => largePrimeTupleHighSum i j ξ Ct (H X) X) =
      fun X => largePrimeTupleOrdinaryHighSum i j ξ δ Ct (H X) X +
        largePrimeTupleExceptionalHighSum i j ξ δ Ct (H X) X := by
    funext X
    exact largePrimeTupleHighSum_split i j ξ δ Ct (H X) X
  rw [hs]
  exact ho.add he

end CubicFirstMoment

end

end OAI
