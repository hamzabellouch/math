import OAI.NumberTheory.CubicMoment.Angular.AngularLargeTupleHighSum
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralAngularLargeTupleExceptionalHigh
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralAngularLargeTupleOrdinarySum

namespace OAI

/-! All high boxes of each actual large-row arity are negligible. The
separate sharp-cutoff boundary contribution is retained explicitly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)


theorem angular_largePrimeTupleHighSum_isLittleO_actual (i j : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) (hδ1 : δ ≤ 1/12)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => angular_largePrimeTupleHighSum ℓ i j ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  have ho := angular_largePrimeTupleOrdinaryHighSum_isLittleO_actual ℓ i j hSW hℓ hpub hHuxley hperiod
    hMV hC hξ hξz hδ hGI hGQ  hGamma Ct H hH
  have he : (fun X => angular_largePrimeTupleExceptionalHighSum ℓ i j ξ δ Ct (H X) X)
      =o[atTop] firstMomentScale := by
    by_cases hij : i+j = 3
    · exact angular_largePrimeTupleExceptionalHighSum_isLittleO_actual ℓ i j hij hpnt hSW hℓ hpub hHuxley
        hperiod hMV hC hξ hξz hδ1 hGI hGQ  hGamma Ct H hH
    · have hz : (fun X => angular_largePrimeTupleExceptionalHighSum ℓ i j ξ δ Ct (H X) X) =
          fun _ : ℝ => (0:ℂ) := by
        funext X
        exact angular_largePrimeTupleExceptionalHighSum_zero ℓ i j hij ξ δ Ct (H X) X
      rw [hz]
      exact Asymptotics.isLittleO_zero _ _
  have hs : (fun X => angular_largePrimeTupleHighSum ℓ i j ξ Ct (H X) X) =
      fun X => angular_largePrimeTupleOrdinaryHighSum ℓ i j ξ δ Ct (H X) X +
        angular_largePrimeTupleExceptionalHighSum ℓ i j ξ δ Ct (H X) X := by
    funext X
    exact angular_largePrimeTupleHighSum_split ℓ i j ξ δ Ct (H X) X
  rw [hs]
  exact ho.add he

end CubicFirstMoment

end

end OAI
