import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCoefficient
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedMellinRows
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedMellinIntegral
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMellinIntegral
import OAI.NumberTheory.CubicMoment.Estimates.MellinConjugation

namespace OAI

/-! The reflected arithmetic kernel follows by conjugating the fixed smooth
weight. The stopped coefficients, selected interval, and all divisor rows
are unchanged. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_reflected_arithmetic_mellin_integral
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (m : ℝ) (hm : 0 < m) (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k q H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V B : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ b^(3/5:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S U : Finset Eisenstein),
      (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      (∀ p ∈ U, primaryPrime p) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ (-t)‖*
        angularStoppedDivisorMass ℓ X (X^ξ) (X^(2/5:ℝ)) l b (t+u) W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early) e S U) ≤ K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  have hΦc : HasCompactSupport (fun x => star (Φ x)) :=
    hΦ.comp_left (show star (0:ℂ) = 0 from star_zero _)
  have hΦc' : ContDiff ℝ ∞ (fun x => star (Φ x)) :=
    Complex.conjCLE.contDiff.comp hΦ'
  have he := angular_stopped_arithmetic_mellin_integral (ι := ι) (E := E)
    hpnt hEF ℓ hℓ hMV hC hHuxley hξ hξz hκ hF hJ
    m hm (fun x => star (Φ x)) hΦc hΦc' k q H
  simpa only [arithmeticMellinCoefficient_conj m hm Φ hΦ hΦ' hΦc hΦc',norm_star] using he

end CubicFirstMoment

end

end OAI
