import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstCentralNegligible
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralScaleFirstEarlyNegligible
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralScaleFirstStoppedReduction

namespace OAI

/-! The original radial low-height prime kernel is negligible, after
choosing the genuine two-stage logarithmic boundary. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem primeProductLowHeight_radial_isLittleO_actual
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξsmall : ξ < 1/100)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => primeProductLowHeight 0 (H X) ((1+Real.log X)^Ct) X)
      =o[atTop] firstMomentScale := by
  let ε := (1/100-ξ)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : ξ+ε < 1/100 := by dsimp [ε]; linarith
  have hcap : 1 < (2:ℝ)^ε := Real.one_lt_rpow (by norm_num) hε
  have hξz : ξ ≤ 2/5 := by linarith
  obtain ⟨m,ρ,hρ,hρ₂,hsmall,hred⟩ := primeProductLowHeight_sub_stopped_isLittleO_actual
    hpnt hSW hpub hHuxley hperiod hMV hC hξ hξz hGI hGQ  hGamma Ct hcap
  obtain ⟨G,hearly⟩ := scaleFirstStoppedEarly_isLittleO_actual m hpnt hSW hMV hC hHuxley
     hGamma hξ hξz hρ hρ₂ hε.le hsmall hgap Ct
  let P (X : ℝ) (h : ℕ) : Prop :=
    h < geometricBinCount ρ (Real.exp primeProductWeights.radius*X) ∧
    geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h ∧
    2*(Real.log X)^G ≤ min (X^ξ)
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) h) ∧
    ρ*geometricBinLower ρ (Real.exp primeProductWeights.radius*X) h ≤ (Real.log X)^(G+4)
  let h (X : ℝ) : ℕ := Classical.epsilon (P X)
  have hspec : ∀ᶠ X : ℝ in atTop, P X (h X) := by
    filter_upwards [eventually_stopping_active_boundary_envelope hξ G,
      eventually_ge_atTop (1:ℝ)] with X hb hX
    apply Classical.epsilon_spec
    exact hb (Real.exp primeProductWeights.radius*X)
      (le_mul_of_one_le_left (zero_lt_one.trans_le hX).le
        (Real.one_le_exp primeProductWeights.radius_nonneg)) ρ hρ hρ₂
  have hindex : ∀ᶠ X : ℝ in atTop,
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h X :=
    hspec.mono (fun _ hx => hx.2.1)
  have hrough : ∀ᶠ X : ℝ in atTop, 2*(Real.log X)^G ≤ min (X^ξ)
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X)) :=
    hspec.mono (fun _ hx => hx.2.2.1)
  have hboundary : ∀ᶠ X : ℝ in atTop,
      ρ*geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X) ≤
        (Real.log X)^((G+4:ℕ):ℝ) :=
    hspec.mono (fun X hx => by simpa only [Real.rpow_natCast] using hx.2.2.2)
  have he := hearly H h hH hindex hrough
  have hl := scaleFirstStoppedLate_isLittleO m hpnt
    (show (0:ℝ) < ((G+4:ℕ):ℝ) by positivity) hξ hρ hρ₂ hε.le hsmall hgap Ct H h
    hH hindex hboundary
  apply ((hred H hH h).add (he.add hl)).congr' ?_ Filter.EventuallyEq.rfl
  exact Filter.Eventually.of_forall (fun X => by dsimp; ring)

end CubicFirstMoment

end

end OAI
